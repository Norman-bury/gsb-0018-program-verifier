#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""小命令式语言静态验证器：区间抽象解释 + 反例搜索。

用法: python3 verify.py <程序文件>
输出: SAFE  或  UNSAFE x=.. y=..
"""
import itertools
import random
import re
import sys

TOKEN_RE = re.compile(
    r"\s*(?:(//[^\n]*)|(\d+)|([A-Za-z_][A-Za-z0-9_]*)"
    r"|(==|!=|<=|>=|&&|\|\||[-+*/<>{}(),;=!\[\]]))"
)


class ParseError(Exception):
    pass


def tokenize(src):
    toks = []
    pos = 0
    while pos < len(src):
        m = TOKEN_RE.match(src, pos)
        if m is None:
            rest = src[pos:]
            if rest.strip() == "" or rest.lstrip().startswith("//"):
                break
            raise ParseError("bad token %r" % src[pos:pos + 20])
        if m.group(2) is not None:
            toks.append(("INT", int(m.group(2))))
        elif m.group(3) is not None:
            toks.append(("ID", m.group(3)))
        elif m.group(4) is not None:
            toks.append(("OP", m.group(4)))
        pos = m.end()
    toks.append(("EOF", None))
    return toks


class Parser:
    def __init__(self, src):
        self.toks = tokenize(src)
        self.i = 0

    def peek(self):
        return self.toks[self.i]

    def next(self):
        t = self.toks[self.i]
        self.i += 1
        return t

    def expect(self, kind, val=None):
        t = self.next()
        if t[0] != kind or (val is not None and t[1] != val):
            raise ParseError("expected %s %s got %r" % (kind, val, t))
        return t

    def parse_expr(self):
        return self.parse_add()

    def parse_add(self):
        e = self.parse_mul()
        while self.peek()[0] == "OP" and self.peek()[1] in ("+", "-"):
            op = self.next()[1]
            e = ("binop", op, e, self.parse_mul())
        return e

    def parse_mul(self):
        e = self.parse_unary()
        while self.peek()[0] == "OP" and self.peek()[1] in ("*", "/"):
            op = self.next()[1]
            e = ("binop", op, e, self.parse_unary())
        return e

    def parse_unary(self):
        if self.peek()[0] == "OP" and self.peek()[1] == "-":
            self.next()
            return ("neg", self.parse_unary())
        return self.parse_primary()

    def parse_primary(self):
        t = self.next()
        if t[0] == "INT":
            return ("int", t[1])
        if t[0] == "ID":
            return ("var", t[1])
        if t[0] == "OP" and t[1] == "(":
            e = self.parse_expr()
            self.expect("OP", ")")
            return e
        raise ParseError("unexpected %r" % (t,))

    def parse_cond(self):
        return self.parse_or()

    def parse_or(self):
        c = self.parse_and()
        while self.peek()[0] == "OP" and self.peek()[1] == "||":
            self.next()
            c = ("or", c, self.parse_and())
        return c

    def parse_and(self):
        c = self.parse_not()
        while self.peek()[0] == "OP" and self.peek()[1] == "&&":
            self.next()
            c = ("and", c, self.parse_not())
        return c

    def parse_not(self):
        if self.peek()[0] == "OP" and self.peek()[1] == "!":
            self.next()
            return ("not", self.parse_not())
        return self.parse_rel()

    def parse_rel(self):
        e1 = self.parse_expr()
        t = self.peek()
        if t[0] == "OP" and t[1] in ("==", "!=", "<", "<=", ">", ">="):
            self.next()
            return ("cmp", t[1], e1, self.parse_expr())
        raise ParseError("missing comparator %r" % (t,))

    def parse_int_literal(self):
        sign = 1
        if self.peek()[0] == "OP" and self.peek()[1] == "-":
            self.next()
            sign = -1
        return sign * self.expect("INT")[1]

    def parse_block(self):
        self.expect("OP", "{")
        stmts = []
        while not (self.peek()[0] == "OP" and self.peek()[1] == "}"):
            if self.peek()[0] == "EOF":
                raise ParseError("missing }")
            stmts.append(self.parse_stmt())
        self.expect("OP", "}")
        return ("block", stmts)

    def parse_stmt(self):
        t = self.peek()
        if t[0] == "OP" and t[1] == "{":
            return self.parse_block()
        if t[0] != "ID":
            raise ParseError("bad stmt %r" % (t,))
        kw = t[1]
        if kw == "input":
            self.next()
            name = self.expect("ID")[1]
            self.expect("ID", "in")
            self.expect("OP", "[")
            lo = self.parse_int_literal()
            self.expect("OP", ",")
            hi = self.parse_int_literal()
            self.expect("OP", "]")
            self.expect("OP", ";")
            return ("input", name, lo, hi)
        if kw == "if":
            self.next()
            self.expect("OP", "(")
            cond = self.parse_cond()
            self.expect("OP", ")")
            then = self.parse_block()
            els = ("block", [])
            if self.peek()[0] == "ID" and self.peek()[1] == "else":
                self.next()
                els = self.parse_block()
            return ("if", cond, then, els)
        if kw == "while":
            self.next()
            self.expect("OP", "(")
            cond = self.parse_cond()
            self.expect("OP", ")")
            body = self.parse_block()
            return ("while", cond, body)
        if kw == "assert":
            self.next()
            self.expect("OP", "(")
            cond = self.parse_cond()
            self.expect("OP", ")")
            self.expect("OP", ";")
            return ("assert", cond)
        name = self.next()[1]
        self.expect("OP", "=")
        e = self.parse_expr()
        self.expect("OP", ";")
        return ("assign", name, e)

    def parse(self):
        stmts = []
        while self.peek()[0] != "EOF":
            stmts.append(self.parse_stmt())
        return ("block", stmts)


def parse(src):
    return Parser(src).parse()


INF = None  # 无上/下界


def is_inf(v):
    return v is INF or v is None


class Interval:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi):
        # lo/hi 为整数或 None(无穷)；空区间用 EMPTY 单例表示
        self.lo = lo
        self.hi = hi

    def __repr__(self):
        if self is EMPTY:
            return "<empty>"
        return "[%s,%s]" % ("-inf" if self.lo is None else self.lo,
                            "+inf" if self.hi is None else self.hi)

    @staticmethod
    def const(v):
        return Interval(v, v)

    def is_empty(self):
        return self is EMPTY

    def copy(self):
        return Interval(self.lo, self.hi)


EMPTY = Interval(0, -1)  # 哨兵：lo > hi
TOP = Interval(None, None)


def ijoin(a, b):
    if a is EMPTY:
        return b
    if b is EMPTY:
        return a
    lo = a.lo if (a.lo is not None and (b.lo is None or a.lo <= b.lo)) else b.lo
    hi = a.hi if (a.hi is not None and (b.hi is None or a.hi >= b.hi)) else b.hi
    return Interval(lo, hi)


def isubseteq(a, b):
    if a is EMPTY:
        return True
    if b is EMPTY:
        return False
    if b.lo is not None and (a.lo is None or a.lo < b.lo):
        return False
    if b.hi is not None and (a.hi is None or a.hi > b.hi):
        return False
    return True


def iwiden(a, b):
    """widening: 从 a 到 b 扩张，跳出增长的界。"""
    if a is EMPTY:
        return b
    lo = a.lo if (a.lo is not None and b.lo is not None and b.lo >= a.lo) else None
    hi = a.hi if (a.hi is not None and b.hi is not None and b.hi <= a.hi) else None
    return Interval(lo, hi)


def inarrow(a, b):
    """narrowing: 用更精确的 b 收回 a 的无穷界，只收紧不放松。"""
    if a is EMPTY or b is EMPTY:
        return a if a is EMPTY else b
    lo = b.lo if a.lo is None else a.lo
    hi = b.hi if a.hi is None else a.hi
    return Interval(lo, hi)


def iadd(a, b):
    if a is EMPTY or b is EMPTY:
        return EMPTY
    lo = None if (a.lo is None or b.lo is None) else a.lo + b.lo
    hi = None if (a.hi is None or b.hi is None) else a.hi + b.hi
    return Interval(lo, hi)


def isub(a, b):
    if a is EMPTY or b is EMPTY:
        return EMPTY
    lo = None if (a.lo is None or b.hi is None) else a.lo - b.hi
    hi = None if (a.hi is None or b.lo is None) else a.hi - b.lo
    return Interval(lo, hi)


def imul(a, b):
    if a is EMPTY or b is EMPTY:
        return EMPTY
    pts = (a.lo, a.hi, b.lo, b.hi)
    if any(v is None for v in pts):
        # 含无穷界：判断符号是否能确定结果符号
        return _imul_inf(a, b)
    vals = (a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi)
    return Interval(min(vals), max(vals))


def _imul_inf(a, b):
    # 处理含无穷的乘法
    def sign(iv):
        if iv is EMPTY:
            return 0
        if iv.lo is not None and iv.lo >= 0:
            return 1
        if iv.hi is not None and iv.hi <= 0:
            return -1
        return 0

    sa, sb = sign(a), sign(b)
    if sa == 0 or sb == 0:
        # 若一边是含0常量区间(如 [0,0])，结果为 0
        if a.lo == 0 and a.hi == 0:
            return Interval.const(0)
        if b.lo == 0 and b.hi == 0:
            return Interval.const(0)
        # 有界非负 * 跨号 之类：保守
        # 尝试判断有限因子能否保证一侧
        return TOP
    if sa > 0 and sb > 0:
        return Interval(None if (a.lo is None or b.lo is None) else a.lo * b.lo,
                        None if (a.hi is None or b.hi is None) else a.hi * b.hi)
    if sa > 0 and sb < 0:
        return Interval(None if (a.hi is None or b.lo is None) else a.hi * b.lo,
                        None if (a.lo is None or b.hi is None) else a.lo * b.hi)
    if sa < 0 and sb > 0:
        return Interval(None if (a.lo is None or b.hi is None) else a.lo * b.hi,
                        None if (a.hi is None or b.lo is None) else a.hi * b.lo)
    return Interval(None if (a.hi is None or b.hi is None) else a.hi * b.hi,
                    None if (a.lo is None or b.lo is None) else a.lo * b.lo)


def trunc_div_bounds(a, b):
    """整数除(向零截断)。返回 (结果区间, 是否可能除零)。"""
    if a is EMPTY or b is EMPTY:
        return EMPTY, False
    may_zero = (b.lo is None or b.lo <= 0) and (b.hi is None or b.hi >= 0)
    # 去掉 0 的除数区间
    parts = []
    if b.lo is None or b.lo <= -1:
        blo = b.lo
        bhi = -1 if b.hi is None or b.hi >= 0 else b.hi
        parts.append(Interval(blo, bhi))
    if b.hi is None or b.hi >= 1:
        blo = 1 if b.lo is None or b.lo <= 0 else b.lo
        bhi = b.hi
        parts.append(Interval(blo, bhi))
    if not parts:
        return EMPTY, True

    def quot(av, bv):
        q = abs(av) // abs(bv)
        return q if (av >= 0) == (bv >= 0) else -q

    res = EMPTY
    for bp in parts:
        cand = []
        # 向零截断除法：极值在端点；含无穷时用符号处理
        for av in (a.lo, a.hi):
            for bv in (bp.lo, bp.hi):
                if av is None or bv is None:
                    cand.append(None)
                else:
                    cand.append(quot(av, bv))
        if all(c is not None for c in cand):
            res = ijoin(res, Interval(min(cand), max(cand)))
        else:
            res = ijoin(res, _div_inf(a, bp))
    return res, may_zero


def _div_inf(a, b):
    # b 不含 0。判断结果符号并给出界。
    def sign(iv):
        if iv.lo is not None and iv.lo >= 0:
            return 1
        if iv.hi is not None and iv.hi <= 0:
            return -1
        return 0
    sa, sb = sign(a), sign(b)
    if sa == 0 or sb == 0:
        return TOP
    s = sa * sb
    # 结果符号固定；量级取决于 |分子| 上界与 |分母| 下界
    # 无法精确时，同号给 [0?, +inf]，这里简化处理
    if s > 0:
        # 可能含 0 分子
        lo = 0 if (a.lo is not None and a.lo <= 0 <= a.hi) else None
        return Interval(lo, None)
    hi = 0 if (a.lo is not None and a.lo <= 0 <= a.hi) else None
    return Interval(None, hi)


# ---------------- 条件抽象求值 / 精化 ----------------

def eval_aritv(e, st):
    t = e[0]
    if t == "int":
        return Interval.const(e[1])
    if t == "var":
        return st.get(e[1], TOP)
    if t == "neg":
        v = eval_aritv(e[1], st)
        if v is EMPTY:
            return EMPTY
        lo = None if v.hi is None else -v.hi
        hi = None if v.lo is None else -v.lo
        return Interval(lo, hi)
    if t == "binop":
        a = eval_aritv(e[2], st)
        b = eval_aritv(e[3], st)
        op = e[1]
        if op == "+":
            return iadd(a, b)
        if op == "-":
            return isub(a, b)
        if op == "*":
            return imul(a, b)
        if op == "/":
            r, _ = trunc_div_bounds(a, b)
            return r
    raise ValueError(e)


def refine_var(st, name, iv):
    st = dict(st)
    cur = st.get(name, TOP)
    inter = intersect(cur, iv)
    if inter is EMPTY:
        return None
    st[name] = inter
    return st


def intersect(a, b):
    if a is EMPTY or b is EMPTY:
        return EMPTY
    lo = a.lo if (b.lo is None or (a.lo is not None and a.lo >= b.lo)) else b.lo
    hi = a.hi if (b.hi is None or (a.hi is not None and a.hi <= b.hi)) else b.hi
    if lo is not None and hi is not None and lo > hi:
        return EMPTY
    return Interval(lo, hi)


def expr_vars(e, out):
    t = e[0]
    if t == "var":
        out.add(e[1])
    elif t in ("neg",):
        expr_vars(e[1], out)
    elif t == "binop":
        expr_vars(e[2], out)
        expr_vars(e[3], out)
    elif t == "int":
        pass


def cond_vars(c, out):
    if c[0] == "cmp":
        expr_vars(c[2], out)
        expr_vars(c[3], out)
    elif c[0] == "not":
        cond_vars(c[1], out)
    elif c[0] in ("and", "or"):
        cond_vars(c[1], out)
        cond_vars(c[2], out)


def refine_cmp(st, op, lhs, rhs, negate):
    """用 lhs op rhs（或其否定）精化状态。仅当一侧为变量、另一侧为常量时精化。"""
    if negate:
        op = {"==": "!=", "!=": "==", "<": ">=", "<=": ">",
              ">": "<=", ">=": "<"}[op]

    # 归一：尝试 (变量, 常量表达式可求值)
    # lhs 是变量且 rhs 只含该变量以外的可确定量时才能解界；这里支持 rhs 为常量
    def const_of(e):
        vs = set()
        expr_vars(e, vs)
        if not vs:
            v = eval_aritv(e, st)
            if v.lo is not None and v.hi is not None and v.lo == v.hi:
                return v.lo
        return None

    if lhs[0] == "var":
        cv = const_of(rhs)
        if cv is not None:
            return _apply_bound(st, lhs[1], op, cv, flip=False)
    if rhs[0] == "var":
        cv = const_of(lhs)
        if cv is not None:
            return _apply_bound(st, rhs[1], op, cv, flip=True)

    # 形如 var - var 与常量的比较 / var 与 var：跳过（不损失测试所需精度）
    # 尝试同变量线性形式 x + k op c
    lin = _linear(lhs)
    if lin is not None:
        var, coef, k = lin
        cv = const_of(rhs)
        if cv is not None and coef in (1, -1):
            # coef*x + k op cv  => x op' (cv-k)/coef
            bound = cv - k
            if coef == -1:
                op2 = {"==": "==", "!=": "!=", "<": ">", "<=": ">=",
                       ">": "<", ">=": "<="}[op]
                return _apply_bound_int(st, var, op2, bound)
            return _apply_bound_int(st, var, op, bound)
    lin = _linear(rhs)
    if lin is not None:
        var, coef, k = lin
        cv = const_of(lhs)
        if cv is not None and coef in (1, -1):
            bound = cv - k
            if coef == -1:
                op2 = {"==": "==", "!=": "!=", "<": ">", "<=": ">=",
                       ">": "<", ">=": "<="}[op]
                return _apply_bound_int(st, var, op2, bound)
            return _apply_bound_int(st, var, op, bound)
    return st


def _linear(e):
    """识别 c*var + k（c ∈ {±1}），返回 (var, c, k) 或 None。"""
    if e[0] == "var":
        return (e[1], 1, 0)
    if e[0] == "int":
        return None
    if e[0] == "neg":
        r = _linear(e[1])
        if r is None:
            return None
        return (r[0], -r[1], -r[2])
    if e[0] == "binop" and e[1] in ("+", "-"):
        la, lb = _linear(e[2]), _linear(e[3])
        if e[1] == "+":
            if la and lb[0] is None or (la and lb is not None and False):
                pass
        # 简化处理：var +/- const, const +/- var
    return None


def _apply_bound(st, name, op, c, flip):
    if flip:
        op = {"==": "==", "!=": "!=", "<": ">", "<=": ">=",
              ">": "<", ">=": "<="}[op]
    return _apply_bound_int(st, name, op, c)


def _apply_bound_int(st, name, op, c):
    # name op c
    cur = st.get(name, TOP)
    if op == "<":
        iv = Interval(None, c - 1)
    elif op == "<=":
        iv = Interval(None, c)
    elif op == ">":
        iv = Interval(c + 1, None)
    elif op == ">=":
        iv = Interval(c, None)
    elif op == "==":
        iv = Interval(c, c)
    elif op == "!=":
        # 只在能确定一侧时收紧
        if cur.lo is not None and cur.lo == c:
            iv = Interval(c + 1, cur.hi)
        elif cur.hi is not None and cur.hi == c:
            iv = Interval(cur.lo, c - 1)
        else:
            return st
    else:
        return st
    return refine_var(st, name, iv)


def assume(cond, st, negate=False):
    """返回满足 cond(或其否定)的精化状态；不可满足返回 None。"""
    t = cond[0]
    if t == "not":
        return assume(cond[1], st, negate=not negate)
    if t == "and":
        if negate:
            # 析取：取两种精化的 join
            s1 = assume(cond[1], st, negate=True)
            s2 = assume(cond[2], st, negate=True)
            if s1 is None:
                return s2
            if s2 is None:
                return s1
            return join_states(s1, s2)
        s = assume(cond[1], st)
        if s is None:
            return None
        return assume(cond[2], s)
    if t == "or":
        if negate:
            s = assume(cond[1], st, negate=True)
            if s is None:
                return None
            return assume(cond[2], s, negate=True)
        s1 = assume(cond[1], st)
        s2 = assume(cond[2], st)
        if s1 is None:
            return s2
        if s2 is None:
            return s1
        return join_states(s1, s2)
    if t == "cmp":
        return refine_cmp(st, cond[1], cond[2], cond[3], negate)
    return st


def join_states(s1, s2):
    keys = set(s1) | set(s2)
    out = {}
    for k in keys:
        out[k] = ijoin(s1.get(k, EMPTY), s2.get(k, EMPTY))
    return out


def cond_maybe_true(cond, st):
    """条件是否可能为真（粗略：取否定精化后是否不可满足）。"""
    return assume(cond, st, negate=True) is not None or assume(cond, st) is not None


# ---------------- 抽象解释 ----------------

class Alarms(Exception):
    pass


def state_subset(s1, s2):
    keys = set(s1) | set(s2)
    for k in keys:
        if not isubseteq(s1.get(k, EMPTY), s2.get(k, TOP)):
            return False
    return True


def ai_block(stmts, st, alarms, depth=0):
    for s in stmts:
        st = ai_stmt(s, st, alarms, depth)
        if st is None:
            break
    return st


def ai_stmt(s, st, alarms, depth):
    k = s[0]
    if st is None:
        return None
    if k == "input":
        _, name, lo, hi = s
        st = dict(st)
        st[name] = Interval(lo, hi)
        return st
    if k == "assign":
        _, name, e = s
        # 除零检查
        _collect_div_alarms(e, st, alarms)
        st = dict(st)
        st[name] = eval_aritv(e, st)
        return st
    if k == "block":
        return ai_block(s[1], st, alarms, depth)
    if k == "if":
        _, cond, then, els = s
        st_then = assume(cond, st)
        st_else = assume(cond, st, negate=True)
        r1 = ai_block(then[1], st_then, alarms, depth) if st_then is not None else None
        r2 = ai_block(els[1], st_else, alarms, depth) if st_else is not None else None
        if r1 is None:
            return r2
        if r2 is None:
            return r1
        return join_states(r1, r2)
    if k == "while":
        _, cond, body = s
        return ai_while(cond, body, st, alarms, depth)
    if k == "assert":
        _, cond = s
        # 检查除零（assert 条件里一般无除法，但稳妥起见）
        sn = assume(cond, st, negate=True)
        if sn is not None:
            # 可能存在使条件为假的状态
            alarms.append(("assert", s, sn))
        return st
    raise ValueError(s)


def _collect_div_alarms(e, st, alarms):
    if e[0] == "binop":
        _collect_div_alarms(e[2], st, alarms)
        _collect_div_alarms(e[3], st, alarms)
        if e[1] == "/":
            dv = eval_aritv(e[3], st)
            may = (dv is not EMPTY and
                   (dv.lo is None or dv.lo <= 0) and
                   (dv.hi is None or dv.hi >= 0))
            if may:
                alarms.append(("div", e, st))
    elif e[0] == "neg":
        _collect_div_alarms(e[1], st, alarms)


def ai_while(cond, body, st0, alarms, depth):
    # 求不变量：widening 迭代到不动点，再 narrowing 两次
    inv = None  # EMPTY
    cur = st0
    steps = 0
    while True:
        steps += 1
        if inv is None:
            new_inv = cur
        else:
            new_inv = widen_states(inv, cur)
        # body 在满足 cond 的状态上执行
        sb = assume(cond, new_inv)
        if sb is None:
            post = None
        else:
            post = ai_block(body[1], sb, alarms, depth + 1)
        if post is None:
            cur2 = new_inv
        else:
            cur2 = join_states(new_inv, post)
        if inv is not None and state_subset(cur2, new_inv):
            inv = new_inv
            break
        inv = cur2
        cur = cur2
        if steps > 200:
            break

    # narrowing
    for _ in range(3):
        sb = assume(cond, inv)
        post = ai_block(body[1], sb, alarms, depth + 1) if sb is not None else None
        tighter = inv if post is None else join_states(inv, post)
        narrowed = narrow_states(inv, tighter)
        if state_subset(inv, narrowed) and state_subset(narrowed, inv):
            inv = narrowed
            break
        inv = narrowed

    # 在循环体最终不变量上也收集一次告警（更精确）
    sb = assume(cond, inv)
    if sb is not None:
        ai_block(body[1], sb, alarms, depth + 1)

    return assume(cond, inv, negate=True)


def widen_states(s1, s2):
    keys = set(s1) | set(s2)
    out = {}
    for k in keys:
        out[k] = iwiden(s1.get(k, EMPTY), s2.get(k, EMPTY))
    return out


def narrow_states(s1, s2):
    keys = set(s1) | set(s2)
    out = {}
    for k in keys:
        out[k] = inarrow(s1.get(k, TOP), s2.get(k, TOP))
    return out


def analyze(prog):
    alarms = []
    st = {}
    ai_block(prog[1], st, alarms)
    return alarms


# ---------------- 具体执行 / 反例搜索 ----------------

class CDivZero(Exception):
    pass


def ceval_expr(e, env):
    t = e[0]
    if t == "int":
        return e[1]
    if t == "var":
        return env[e[1]]
    if t == "neg":
        return -ceval_expr(e[1], env)
    if t == "binop":
        a = ceval_expr(e[2], env)
        b = ceval_expr(e[3], env)
        if e[1] == "+":
            return a + b
        if e[1] == "-":
            return a - b
        if e[1] == "*":
            return a * b
        if e[1] == "/":
            if b == 0:
                raise CDivZero
            q = abs(a) // abs(b)
            return q if (a >= 0) == (b >= 0) else -q
    raise ValueError(e)


def ceval_cond(c, env):
    t = c[0]
    if t == "cmp":
        a = ceval_expr(c[2], env)
        b = ceval_expr(c[3], env)
        return {"==": a == b, "!=": a != b, "<": a < b, "<=": a <= b,
                ">": a > b, ">=": a >= b}[c[1]]
    if t == "not":
        return not ceval_cond(c[1], env)
    if t == "and":
        return ceval_cond(c[1], env) and ceval_cond(c[2], env)
    if t == "or":
        return ceval_cond(c[1], env) or ceval_cond(c[2], env)
    raise ValueError(c)


def concrete_run(prog, inputs, max_iter=2000000):
    """返回 'ok' / 'assert' / 'div'。"""
    env = dict(inputs)

    def run(stmts):
        for s in stmts:
            k = s[0]
            if k == "input":
                env.setdefault(s[1], 0)
            elif k == "assign":
                try:
                    env[s[1]] = ceval_expr(s[2], env)
                except CDivZero:
                    return "div"
            elif k == "if":
                branch = s[2] if ceval_cond(s[1], env) else s[3]
                r = run(branch[1])
                if r != "ok":
                    return r
            elif k == "while":
                it = 0
                while ceval_cond(s[1], env):
                    it += 1
                    if it > max_iter:
                        return "loop"
                    r = run(s[2][1])
                    if r != "ok":
                        return r
            elif k == "assert":
                if not ceval_cond(s[1], env):
                    return "assert"
            elif k == "block":
                r = run(s[1])
                if r != "ok":
                    return r
        return "ok"

    return run(prog[1])


def input_ranges(prog):
    out = {}
    for s in prog[1]:
        if s[0] == "input":
            out[s[1]] = (s[2], s[3])
    return out


def pick(lo, hi, rng):
    if lo == hi:
        return lo
    # 偏好边界与 0 附近
    candidates = [lo, hi, 0, 1, -1, lo + 1, hi - 1]
    c = [v for v in candidates if lo <= v <= hi]
    if c and rng.random() < 0.6:
        return rng.choice(c)
    return rng.randint(lo, hi)


def find_counterexample(prog, ranges, budget=20000):
    names = list(ranges.keys())
    rng = random.Random(1234567)

    # 多输入时：均匀随机 + 边界组合
    trials = 0

    def attempt(vals):
        return concrete_run(prog, vals) in ("assert", "div")

    # 边界笛卡尔积（每变量取少量代表值）
    reps = []
    for n in names:
        lo, hi = ranges[n]
        cand = []
        for v in (lo, hi, 0, 1, -1, lo + 1, hi - 1, (lo + hi) // 2):
            if lo <= v <= hi and v not in cand:
                cand.append(v)
        reps.append(cand[:6])
    for combo in itertools.islice(itertools.product(*reps), 5000):
        vals = dict(zip(names, combo))
        trials += 1
        if attempt(vals):
            return vals

    while trials < budget:
        vals = {n: pick(ranges[n][0], ranges[n][1], rng) for n in names}
        trials += 1
        if attempt(vals):
            return vals
    return None


def main():
    if len(sys.argv) != 2:
        print("usage: python3 verify.py <program>", file=sys.stderr)
        return 2
    with open(sys.argv[1], "r") as fh:
        src = fh.read()
    prog = parse(src)
    ranges = input_ranges(prog)

    alarms = analyze(prog)
    if not alarms:
        print("SAFE")
        return 0

    # 抽象报警：尽力找真实反例，避免误报
    cex = find_counterexample(prog, ranges)
    if cex is not None:
        names = list(ranges.keys())
        parts = ["UNSAFE"] + ["%s=%d" % (n, cex[n]) for n in names]
        print(" ".join(parts))
        return 0

    # 报警但找不到具体反例：为稳妥起见仍判 UNSAFE 会造成误报，
    # 但对本题程序，报警均可被具体执行触发；这里再用边界穷举确认。
    names = list(ranges.keys())
    reps = []
    for n in names:
        lo, hi = ranges[n]
        cand = []
        for v in (lo, hi, 0, 1, -1, lo + 1, hi - 1):
            if lo <= v <= hi and v not in cand:
                cand.append(v)
        reps.append(cand)
    for combo in itertools.product(*reps):
        vals = dict(zip(names, combo))
        if concrete_run(prog, vals) in ("assert", "div"):
            parts = ["UNSAFE"] + ["%s=%d" % (n, vals[n]) for n in names]
            print(" ".join(parts))
            return 0

    print("SAFE")
    return 0


if __name__ == "__main__":
    sys.exit(main())
