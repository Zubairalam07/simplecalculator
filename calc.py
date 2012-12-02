#!/usr/bin/python
#
# by Erik Osheim
#
# This program uses a recursive descent, LL1 parser to generate a Code object
# for the given input. Code objects are pure expressions whose behavior can
# only be controlled via a dictionary of strings-to-numbers provided to run.
#
# Syntax:
#
# * decimal numbers (e.g. 3, 4.52)
# * simple names (foo, qux13).
# * built-in constants: pi, e, i
# * arithmetic operators: + - * / % // ^ !
# * parenthesis and absolute value: (2 + 3) * |4 - x|
# * built-in functions:
#   abs, ceil, cos, degrees, floor, log, log10,
#   log2, max, min, radians, round, sin, tan
#
# You can test this program out on the command-line. For instance:
#
#   python calc.py "2 + 2"
#
#   python calc.py "9!"
#
#   python calc.py "2^foo - 1" foo=8
#
#   python calc.py "e^(i*pi) + 1"

import math
import re
import sys

class Lexeme(object):
    def __init__(self, name, pos, data):
        self.name = name
        self.pos = pos
        self.data = data
    def __repr__(self):
        return 'Lexeme(%r, %d, %r)' % (self.name, self.pos, self.data)

class Lexer(object):
    num_re = re.compile(r'(?:0|[1-9][0-9]*)(?:\.[0-9]+)?')

    def __init__(self, data):
        self.data = data

    def lexid(self, i):
        j = i + 1
        while j < len(self.data) and self.data[j].isalnum():
            j += 1
        return Lexeme('id', i, self.data[i:j]), j

    def lexnum(self, i):
        m = self.num_re.match(self.data, i)
        if not m:
            raise Exception("num error for %r at %d" % (self.data, i))
        return Lexeme('num', i, m.group(0)), m.end()

    def lex(self):
        i = 0
        while i < len(self.data):
            c = self.data[i]
            if c.isspace():
                i += 1
            elif c.isalpha():
                lx, i = self.lexid(i)
                yield lx
            elif c.isdigit():
                lx, i = self.lexnum(i)
                yield lx
            elif self.data[i:i + 2] == '//':
                yield Lexeme('//', i, '//')
                i += 2
            else:
                yield Lexeme(c, i, c)
                i += 1
        yield Lexeme('$', i, None)
        raise StopIteration

class Expr(object):
    def __init__(self, op, *args):
        self.op = op
        self.args = args
    def __repr__(self):
        return 'Expr(%r, %r)' % (self.op, self.args)

    def lisp(self):
        if self.op == 'num':
            return self.args[0]
        elif self.op == 'id':
            return self.args[0]
        elif self.op == 'apply':
            return '(%s %s)' % (self.args[0], ' '.join([a.lisp() for a in self.args[1:]]))
        elif self.args:
            return '(%s %s)' % (self.op, ' '.join([a.lisp() for a in self.args]))
        else:
            return self.op

class Parser2(object):
    debug = False

    def error(self):
        if self.debug:
            raise Exception("parse error at %r" % self.cur)
        else:
            raise Exception("parse error at %r (byte %d)" % (self.cur.data, self.cur.pos))

    def __init__(self, data):
        self.lexer = Lexer(data)

    def next(self):
        if self.cur.name == '$':
            self.error()
        try:
            self.cur = self.gen.next()
        except StopIteration:
            self.cur = Lexeme('$', -1, '$')

    def parse(self):
        self.gen = self.lexer.lex()
        self.cur = self.gen.next()
        return self.parseP()

    def lxin(self, *names):
        return self.cur.name in names

    def parseP(self):
        if not self.lxin('num', 'id', '(', '|', '-'): self.error()
        return self.parseE1()

    def parseEx(self, names, f1, f2, right=False):
        if not self.lxin(*names): self.error()
        lhs = f1()
        lst = f2()
        if not lst:
            return lhs
        elif right:
            lst = [lhs] + lst
            expr = lst[-1]
            i = len(lst) - 3
            while i >= 0:
                expr = Expr(lst[i + 1], lst[i], expr)
                i -= 2
            return expr
        else:
            expr = lhs
            i = 0
            while i < len(lst) - 1:
                expr = Expr(lst[i], expr, lst[i + 1])
                i += 2
            return expr

    def parseE1(self):
        return self.parseEx(['num', 'id', '(', '|', '-'], self.parseE2, self.parseE1_)

    def parseE2(self):
        return self.parseEx(['num', 'id', '(', '|', '-'], self.parseE3, self.parseE2_)

    def parseE3(self):
        if self.lxin('-'):
            self.next()
            expr = self.parseE3()
            return Expr('-', expr)
        elif self.lxin('num', 'id', '(', '|'):
            return self.parseE4()
        else:
            self.error()

    def parseE4(self):
        return self.parseEx(['num', 'id', '(', '|'], self.parseE5, self.parseE4_, right=True)

    def parseE5(self):
        if self.lxin('num', 'id', '(', '|'):
            expr = self.parseE6()
            if self.parseE5_() is None:
                return expr
            else:
                return Expr('!', expr)
        else:
            self.error()

    def parseE6(self):
        c = self.cur
        if c.name == 'num':
            self.next()
            return Expr('num', c.data)
        elif c.name == 'id':
            self.next()
            a = self.parseA()
            if a is None:
                return Expr('id', c.data)
            else:
                return Expr('apply', c.data, *a)
        elif c.name == '(':
            self.next()
            e1 = self.parseE1()
            if self.lxin(')'):
                self.next()
                return e1
            else:
                self.error()
        elif c.name == '|':
            self.next()
            e1 = self.parseE1()
            if self.lxin('|'):
                self.next()
                return Expr('abs', e1)
            else:
                self.error()

    def parseA(self):
        if self.lxin('('):
            self.next()
            ll = self.parseL()
            if self.lxin(')'):
                self.next()
                return ll
            else:
                self.error()
        elif self.lxin('!', '$', '^', '*', '/', '//', '%', '+', '-', ')', '|', ','):
            return None
        else:
            self.error()

    def parseL(self):
        if self.lxin('num', 'id', '(', '|', '-'):
            e1 = self.parseE1()
            l_ = self.parseL_()
            if l_ is None:
                return [e1]
            else:
                return [e1] + l_
        else:
            self.error()

    def parseL_(self):
        if self.lxin(','):
            self.next()
            e1 = self.parseE1()
            l_ = self.parseL_()
            if l_ is None:
                return [e1]
            else:
                return [e1] + l_
        elif self.lxin(')'):
            return None
        else:
            self.error()

    def parseEx_(self, names, skips, f1):
        if self.lxin(*names):
            c = self.cur
            self.next()
            lhs = f1()
            lst = self.parseEx_(names, skips, f1)
            return [c.name, lhs] + lst
        elif self.lxin(*skips):
            return []
        else:
            self.error()

    def parseE1_(self):
        return self.parseEx_(['+', '-'], [')', '|', ',', '$'], self.parseE2)

    def parseE2_(self):
        return self.parseEx_(['*', '/', '//', '%'], ['+', '-', '$', ')', '|', ','], self.parseE3)

    def parseE4_(self):
        return self.parseEx_(['^'], ['*', '/', '//', '%', '$', '+', '-', ')', '|', ','], self.parseE5)

    def parseE5_(self):
        if self.lxin('!'):
            self.next()
            if self.parseE5_() is None:
                return '!'
            else:
                return None
        elif self.lxin('^', '$', '*', '/', '//', '%', '+', '-', ')', '|', ','):
            return None
        else:
            self.error()

class Code(object):
    @classmethod
    def gen(cls, e):
        if e.op == 'num':
            if '.' in e.args[0]:
                n = float(e.args[0])
            else:
                n = int(e.args[0])
            return cls(lambda kw: n, [])
        elif e.op == 'id':
            s = e.args[0]
            if s == 'e':
                return cls(lambda kw: math.e, [])
            elif s == 'pi':
                return cls(lambda kw: math.pi, [])
            elif s == 'i':
                return cls(lambda kw: 1j, [])
            else:
                return cls(lambda kw: kw[s], [s])
        elif e.op == '+':
            lhs = Code.gen(e.args[0])
            rhs = Code.gen(e.args[1])
            names = lhs.names + rhs.names
            return cls(lambda kw: lhs.run(kw) + rhs.run(kw), names)
        elif e.op == '-':
            lhs = Code.gen(e.args[0])
            if len(e.args) == 1:
                return cls(lambda kw: -lhs.run(kw), lhs.names)
            else:
                rhs = Code.gen(e.args[1])
                names = lhs.names + rhs.names
                return cls(lambda kw: lhs.run(kw) - rhs.run(kw), names)
        elif e.op == '*':
            lhs = Code.gen(e.args[0])
            rhs = Code.gen(e.args[1])
            names = lhs.names + rhs.names
            return cls(lambda kw: lhs.run(kw) * rhs.run(kw), names)
        elif e.op == '/':
            lhs = Code.gen(e.args[0])
            rhs = Code.gen(e.args[1])
            names = lhs.names + rhs.names
            return cls(lambda kw: lhs.run(kw) / rhs.run(kw), names)
        elif e.op == '%':
            lhs = Code.gen(e.args[0])
            rhs = Code.gen(e.args[1])
            names = lhs.names + rhs.names
            return cls(lambda kw: lhs.run(kw) % rhs.run(kw), names)
        elif e.op == '//':
            lhs = Code.gen(e.args[0])
            rhs = Code.gen(e.args[1])
            names = lhs.names + rhs.names
            return cls(lambda kw: lhs.run(kw) // rhs.run(kw), names)
        elif e.op == '^':
            lhs = Code.gen(e.args[0])
            rhs = Code.gen(e.args[1])
            names = lhs.names + rhs.names
            return cls(lambda kw: lhs.run(kw) ** rhs.run(kw), names)
        elif e.op == '!':
            lhs = Code.gen(e.args[0])
            return cls(lambda kw: math.factorial(lhs.run(kw)), lhs.names)
        elif e.op == 'abs':
            lhs = Code.gen(e.args[0])
            return cls(lambda kw: abs(lhs.run(kw)), lhs.names)
        elif e.op == 'apply':
            fn = e.args[0]
            if fn == 'abs':
                lhs = Code.gen(e.args[1])
                return cls(lambda kw: abs(lhs.run(kw)), lhs.names)
            elif fn == 'ceil':
                lhs = Code.gen(e.args[1])
                return cls(lambda kw: math.ceil(lhs.run(kw)), lhs.names)
            elif fn == 'cos':
                lhs = Code.gen(e.args[1])
                return cls(lambda kw: math.cos(lhs.run(kw)), lhs.names)
            elif fn == 'degrees':
                lhs = Code.gen(e.args[1])
                return cls(lambda kw: math.degrees(lhs.run(kw)), lhs.names)
            elif fn == 'floor':
                lhs = Code.gen(e.args[1])
                return cls(lambda kw: math.floor(lhs.run(kw)), lhs.names)
            elif fn == 'log':
                lhs = Code.gen(e.args[1])
                return cls(lambda kw: math.log(lhs.run(kw)), lhs.names)
            elif fn == 'log10':
                lhs = Code.gen(e.args[1])
                return cls(lambda kw: math.log10(lhs.run(kw)), lhs.names)
            elif fn == 'log2':
                lhs = Code.gen(e.args[1])
                return cls(lambda kw: math.log(lhs.run(kw), 2), lhs.names)
            elif fn == 'max':
                args = [Code.gen(arg) for arg in e.args[1:]]
                names = []
                for arg in args: names.extend(arg.names)
                return cls(lambda kw: min([a.run(kw) for a in args]), names)
            elif fn == 'min':
                args = [Code.gen(arg) for arg in e.args[1:]]
                names = []
                for arg in args: names.extend(arg.names)
                return cls(lambda kw: min([a.run(kw) for a in args]), names)
            elif fn == 'radians':
                lhs = Code.gen(e.args[1])
                return cls(lambda kw: math.radians(lhs.run(kw)), lhs.names)
            elif fn == 'round':
                lhs = Code.gen(e.args[1])
                return cls(lambda kw: round(lhs.run(kw)), lhs.names)
            elif fn == 'sin':
                lhs = Code.gen(e.args[1])
                return cls(lambda kw: math.sin(lhs.run(kw)), lhs.names)
            elif fn == 'tan':
                lhs = Code.gen(e.args[1])
                return cls(lambda kw: math.tan(lhs.run(kw)), lhs.names)
            else:
                raise Exception("function %r is not defined" % e.args[0])
        else:
            raise Exception("can't handle %r" % e)
    def __init__(self, f, names):
        self.f = f
        self.names = names
    def run(self, kw):
        return self.f(kw)

if __name__ == "__main__":
    def tplize(s):
        k, v = s.split('=')
        if '.' in v:
            return (k, float(v))
        else:
            return (k, int(v))

    s = sys.argv[1]
    print "input: %s" % s
    d = dict([tplize(arg) for arg in sys.argv[2:]])

    e = Parser2(s).parse()
    print "lisp: %s" % e.lisp()

    c = Code.gen(e)
    if c.names:
        print "variables used: %s" % ', '.join(c.names)
    else:
        print "no variables"

    try:
        r = c.run(d)
        print "result: %r" % r
    except KeyError, k:
        print "missing variable: %r" % k.message

# Calculator Grammar:
#
# non-terminal productions
#   P   -> E1
#   E1  -> E2 E1_
#   E1_ -> + E2 E1_ | - E2 E1_ | e
#   E2  -> E3 E2_
#   E2_ -> * E3 E2_ | / E3 E2_ | // E3 E2_ | % E3 E2_ | e
#   E3  -> E4 | - E4
#   E4  -> E5 E4_
#   E4_ -> ^ E5 E4_ | e
#   E5  -> E6 E5_
#   E5_ -> ! E5_ | e
#   E6  -> num | id A | ( E1 ) | bar E1 bar
#   A   -> ( L ) | e
#   L   -> E1 L_
#   L_  -> , E1 L_ | e
# 
# terminal definitions
#   bar = "|"
#   id  = [a-zA-Z][a-zA-Z0-9]*
#   num = (0|[1-9][0-9]*)(\.[0-9]+)?
#   (plus other literal characters, e.g. +)
# 
# first sets
#   Fi(A)   = ( e
#   Fi(E6)  = num id ( bar
#   Fi(E5_) = ! e
#   Fi(E5)  = Fi(E6)       = num id ( bar
#   Fi(E4_) = ^ e
#   Fi(E4)  = Fi(E5)       = num id ( bar
#   Fi(E3)  = Fi(E4) -     = num id ( bar -
#   Fi(E2_) = * / // % e
#   Fi(E2)  = Fi(E3)       = num id ( bar -
#   Fi(E1_) = + - e
#   Fi(E1)  = Fi(E2)       = num id ( bar -
#   Fi(P)   = Fi(E1)       = num id ( bar -
#   Fi(L)   = Fi(E1)       = num id ( bar -
#   Fi(L_)  = , e
# 
# follow sets
#   Fo(E1)  = ) bar Fi(L_) Fo(L) = ) bar , e
#   Fo(E1_) = Fo(E1)             = ) bar , e
#   Fo(E2)  = Fi(E1_) Fo(E1)     = + - e ) bar ,
#   Fo(E2_) = Fo(E2)             = + - e ) bar ,
#   Fo(E3)  = Fi(E2_) Fo(E2)     = * / // % e + - ) bar ,
#   Fo(E4)  = Fo(E3)             = * / // % e + - ) bar ,
#   Fo(E4_) = Fo(E4)             = * / // % e + - ) bar ,
#   Fo(E5)  = Fi(E4_) Fo(E4)     = ^ e * / // % + - ) bar ,
#   Fo(E5_) = Fo(E5)             = ^ e * / // % + - ) bar ,
#   Fo(E6)  = Fi(E5_) Fo(E5)     = ! e ^ * / // % + - ) bar ,
#   Fo(A)   = Fo(E6)             = ! e ^ * / // % + - ) bar ,
#   Fo(L)   = )
#   Fo(L_)  = Fo(L)              = )
# 
# parse table (non-terminal, list of terminals = production)
#   P    num id ( bar -             = E1
#   E1   num id ( bar -             = E2 E1_
#   E1_  + -                        = [c] E2 E1_
#   E1_  ) bar , $                  = e
#   E2   num id ( bar -             = E3 E2_
#   E2_  * / // %                   = [c] E3 E2_
#   E2_  + - $ ) bar ,              = e
#   E3   -                          = - E3
#   E3   num id ( bar               = E4
#   E4   num id ( bar               = E5 E4_
#   E4_  ^                          = ^ E5 E4_
#   E4_  * / // % $ + - ) bar ,     = e
#   E5   num id ( bar               = E6 E5_
#   E5_  !                          = ! E5_
#   E5_  ^ $ * / // % + - ) bar ,   = e
#   E6   num                        = num
#   E6   id                         = id A
#   E6   (                          = ( E1 )
#   E6   bar                        = bar E1 bar
#   A    (                          = ( L )
#   A    ! e ^ * / // % + - ) bar , = e
#   L    num id ( bar -             = E1 L_
#   L_   ,                          = , E1 L_
#   L_   )                          = e
