#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""task18（程序验证器 / 区间抽象解释）判分脚本。

规则：
1. 交付 verify.py，命令行入口 `python3 verify.py <程序文件>`。
   程序文件里是小命令式语言源码。verify.py 读进去，判定 assert 有没有可能失败，
   输出 SAFE 或 UNSAFE；UNSAFE 必须给出覆盖全部 input 变量的反例赋值。
2. 判分脚本内置 31 个测试程序（15 SAFE / 16 UNSAFE，覆盖越界、除零、
   循环不变量破坏、除法截断等），并内置该语言的解析器和具体执行解释器，
   用来算真值和复核反例。
3. 对每个程序：写临时文件 → 跑 `python3 verify.py <文件>`（限时）→ 解析输出，
   判定必须与真值一致；UNSAFE 的反例必须真能执行触发（assert 失败或除零）。

用法：
  python3 grade.py
  python3 grade.py --verify path/to/verify.py
"""

import argparse
import itertools
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))

PER_PROGRAM_TIMEOUT = 20  # 单个程序限时，秒


# ======================================================================
# 小命令式语言：词法 + 语法 + 具体执行解释器（判分方自用，算真值、复核反例）
# ======================================================================

TOKEN_RE = re.compile(
    r"\s*(?:(//[^\n]*)|(\d+)|([A-Za-z_][A-Za-z0-9_]*)"
    r"|(==|!=|<=|>=|&&|\|\||[-+*/<>{}(),;=!\[\]]))"
)


class SyntaxError_(Exception):
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
            raise SyntaxError_("无法解析：%r" % src[pos:pos + 20])
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
            raise SyntaxError_("期望 %s %s，得到 %r" % (kind, val, t))
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
        raise SyntaxError_("表达式里出现意外的 %r" % (t,))

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
        raise SyntaxError_("条件里缺少比较运算符：%r" % (t,))

    def parse_int_literal(self):
        sign = 1
        if self.peek()[0] == "OP" and self.peek()[1] == "-":
            self.next()
            sign = -1
        return sign * self.expect("INT")[1]

    def parse_stmt(self):
        t = self.peek()
        if t[0] == "OP" and t[1] == "{":
            return self.parse_block()
        if t[0] != "ID":
            raise SyntaxError_("语句 %r 无法识别" % (t,))
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

    def parse_block(self):
        self.expect("OP", "{")
        stmts = []
        while not (self.peek()[0] == "OP" and self.peek()[1] == "}"):
            if self.peek()[0] == "EOF":
                raise SyntaxError_("缺少 }")
            stmts.append(self.parse_stmt())
        self.expect("OP", "}")
        return ("block", stmts)

    def parse(self):
        stmts = []
        while self.peek()[0] != "EOF":
            stmts.append(self.parse_stmt())
        return ("block", stmts)


def parse(src):
    return Parser(src).parse()


class DivZero(Exception):
    pass


def trunc_div(a, b):
    q = abs(a) // abs(b)
    return q if (a >= 0) == (b >= 0) else -q


def eval_expr(e, env):
    t = e[0]
    if t == "int":
        return e[1]
    if t == "var":
        return env[e[1]]
    if t == "neg":
        return -eval_expr(e[1], env)
    if t == "binop":
        op, a, b = e[1], eval_expr(e[2], env), eval_expr(e[3], env)
        if op == "+":
            return a + b
        if op == "-":
            return a - b
        if op == "*":
            return a * b
        if op == "/":
            if b == 0:
                raise DivZero()
            return trunc_div(a, b)
    raise ValueError(e)


def eval_cond(c, env):
    t = c[0]
    if t == "cmp":
        op, a, b = c[1], eval_expr(c[2], env), eval_expr(c[3], env)
        return {"==": a == b, "!=": a != b, "<": a < b, "<=": a <= b,
                ">": a > b, ">=": a >= b}[op]
    if t == "not":
        return not eval_cond(c[1], env)
    if t == "and":
        return eval_cond(c[1], env) and eval_cond(c[2], env)
    if t == "or":
        return eval_cond(c[1], env) or eval_cond(c[2], env)
    raise ValueError(c)


def exec_stmts(stmts, env, max_iter=1000000):
    for s in stmts:
        k = s[0]
        if k == "input":
            _, name, lo, hi = s
            env[name] = env.get(name, 0)
        elif k == "assign":
            _, name, e = s
            env[name] = eval_expr(e, env)
        elif k == "if":
            _, cond, then, els = s
            branch = then if eval_cond(cond, env) else els
            r = exec_stmts(branch[1], env, max_iter)
            if r[0] != "ok":
                return r
        elif k == "while":
            _, cond, body = s
            it = 0
            while eval_cond(cond, env):
                it += 1
                if it > max_iter:
                    return ("loop", None)
                r = exec_stmts(body[1], env, max_iter)
                if r[0] != "ok":
                    return r
        elif k == "assert":
            _, cond = s
            if not eval_cond(cond, env):
                return ("assert", s)
        elif k == "block":
            r = exec_stmts(s[1], env, max_iter)
            if r[0] != "ok":
                return r
        else:
            raise ValueError(s)
    return ("ok", None)


def run_concrete(prog, inputs):
    env = dict(inputs)
    try:
        return exec_stmts(prog[1], env)
    except DivZero:
        return ("div", None)


def input_vars(prog):
    out = {}
    for s in prog[1]:
        if s[0] == "input":
            out[s[1]] = (s[2], s[3])
    return out


def ground_truth(prog):
    iv = input_vars(prog)
    names = list(iv.keys())
    ranges = [range(iv[n][0], iv[n][1] + 1) for n in names]
    for combo in itertools.product(*ranges):
        inputs = dict(zip(names, combo))
        r = run_concrete(prog, inputs)
        if r[0] in ("assert", "div"):
            return ("UNSAFE", inputs, r[0])
        if r[0] == "loop":
            return ("LOOP", inputs, None)
    return ("SAFE", None, None)


# ======================================================================
# 30 个测试程序（name, source, expected）
# ======================================================================

PROGRAMS = [
    ("bound_ge", "input x in [0,10]; assert(x >= 0);", "SAFE"),
    ("add_ge", "input x in [0,10]; y = x + 5; assert(y >= 5);", "SAFE"),
    ("sub_ge", "input x in [3,10]; y = x - 2; assert(y >= 1);", "SAFE"),
    ("square_ge", "input x in [-5,5]; y = x * x; assert(y >= 0);", "SAFE"),
    ("if_branch", "input x in [-10,10]; if (x >= 0) { assert(x >= 0); } else { assert(x < 0); }", "SAFE"),
    ("div_pos", "input x in [1,10]; y = 100 / x; assert(y >= 10);", "SAFE"),
    ("abs_ge", "input x in [-10,10]; if (x < 0) { y = -x; } else { y = x; } assert(y >= 0);", "SAFE"),
    ("two_inputs", "input a in [0,5]; input b in [0,5]; assert(a + b <= 10);", "SAFE"),
    ("bool_range", "input x in [0,10]; assert(x >= 0 && x <= 10);", "SAFE"),
    ("loop_count_eq", "input n in [0,10]; i = 0; while (i < n) { i = i + 1; } assert(i == n);", "SAFE"),
    ("loop_sum_ge", "input n in [0,10]; i = 0; s = 0; while (i < n) { s = s + i; i = i + 1; } assert(s >= 0);", "SAFE"),
    ("loop_decr_zero", "input n in [0,10]; i = n; while (i > 0) { i = i - 1; } assert(i == 0);", "SAFE"),
    ("nested_if", "input x in [-10,10]; if (x > 0) { if (x > 5) { assert(x > 5); } else { assert(x <= 5 && x > 0); } } else { assert(x <= 0); }", "SAFE"),
    ("div_neg_le", "input x in [-10,-1]; y = x / 2; assert(y <= 0);", "SAFE"),
    ("loop_safe_large", "input n in [0,100000]; i = 0; while (i < n) { i = i + 1; } assert(i >= 0);", "SAFE"),

    ("bound_lt", "input x in [0,10]; assert(x < 5);", "UNSAFE"),
    ("div_zero", "input x in [-5,5]; y = 10 / x; assert(y >= 0);", "UNSAFE"),
    ("loop_off_by_one", "input n in [0,10]; i = 0; while (i < n) { i = i + 1; } assert(i > n);", "UNSAFE"),
    ("loop_sum_neg", "input n in [0,10]; i = 0; s = 0; while (i < n) { s = s + i; i = i + 1; } assert(s < 0);", "UNSAFE"),
    ("square_gt", "input x in [0,10]; y = x * x; assert(y <= 50);", "UNSAFE"),
    ("if_miss", "input x in [0,10]; if (x < 3) { y = 1; } else { y = 2; } assert(y == 1);", "UNSAFE"),
    ("div_trunc", "input x in [1,10]; y = 10 / x; assert(y >= 2);", "UNSAFE"),
    ("abs_bug", "input x in [-10,10]; if (x < 0) { y = x; } else { y = x; } assert(y >= 0);", "UNSAFE"),
    ("loop_le_eq", "input n in [0,10]; i = 0; while (i <= n) { i = i + 1; } assert(i == n);", "UNSAFE"),
    ("bool_or_gap", "input x in [0,10]; assert(x < 5 || x > 8);", "UNSAFE"),
    ("div_neg_ge", "input x in [-10,-1]; y = x / 2; assert(y >= 0);", "UNSAFE"),
    ("loop_sum_eq_n", "input n in [0,10]; i = 0; s = 0; while (i < n) { s = s + 2; i = i + 1; } assert(s == n);", "UNSAFE"),
    ("mul_overflow", "input x in [0,100]; y = x * 3; assert(y <= 200);", "UNSAFE"),
    ("div_zero_loop", "input n in [0,10]; i = 0; while (i < n) { i = i + 1; } x = 1 / (n - i); assert(x >= 0);", "UNSAFE"),
    ("loop_never_assert", "input n in [0,0]; i = 5; while (i < n) { i = i + 1; } assert(i == 0);", "UNSAFE"),
    ("large_unsafe", "input x in [0,2000000000]; assert(x < 1000000000);", "UNSAFE"),
]


def total_combos(prog):
    iv = input_vars(prog)
    t = 1
    for lo, hi in iv.values():
        t *= (hi - lo + 1)
    return t


def self_check():
    """用穷举真值复核内置期望判定（大范围程序跳过，已由出题方 fuzz 验证）。"""
    for name, src, exp in PROGRAMS:
        p = parse(src)
        if total_combos(p) <= 10000:
            gt = ground_truth(p)[0]
            if gt != exp:
                return False, "%s 期望 %s 但穷举真值 %s" % (name, exp, gt)
    return True, ""


def run_verifier(verify_path, src):
    """跑 `verify.py <程序文件>`，返回 (verdict, counterexample_dict_or_None, raw_stdout, stderr)。"""
    fd, path = tempfile.mkstemp(suffix=".txt", prefix="prog_", dir=HERE)
    try:
        with os.fdopen(fd, "w") as fh:
            fh.write(src)
        try:
            r = subprocess.run([sys.executable, verify_path, path],
                               cwd=HERE, capture_output=True, text=True,
                               timeout=PER_PROGRAM_TIMEOUT)
        except subprocess.TimeoutExpired:
            return None, None, "", "超时"
    finally:
        os.unlink(path)
    if r.returncode != 0:
        return None, None, r.stdout, r.stderr[-300:]
    out = r.stdout
    verdict = None
    first = ""
    for line in out.splitlines():
        s = line.strip()
        if s:
            first = s
            break
    m = re.match(r"(SAFE|UNSAFE)\b", first, re.I)
    if m:
        verdict = m.group(1).upper()
    cex = {}
    if verdict == "UNSAFE":
        for name, val in re.findall(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(-?\d+)\b", out):
            cex[name] = int(val)
    return verdict, cex, out, ""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--verify", default=os.path.join(HERE, "verify.py"))
    args = ap.parse_args()

    print("=" * 60)
    print("判分开始")

    if not os.path.exists(args.verify):
        print("[FAIL] 找不到 verify.py（%s）" % args.verify)
        sys.exit(1)

    ok, msg = self_check()
    if not ok:
        print("[FAIL] 判分脚本自检失败：" + msg)
        sys.exit(1)

    fails = 0
    for name, src, exp in PROGRAMS:
        p = parse(src)
        iv = input_vars(p)
        names = list(iv.keys())
        verdict, cex, out, err = run_verifier(args.verify, src)
        if verdict is None:
            print("[FAIL] %-18s 期望 %-6s 验证器运行失败：%s" % (name, exp, err[-120:]))
            fails += 1
            continue
        if verdict != exp:
            print("[FAIL] %-18s 期望 %-6s 得到 %-6s" % (name, exp, verdict))
            fails += 1
            continue
        # UNSAFE：反例必须覆盖全部 input 变量，且真能触发
        if exp == "UNSAFE":
            missing = [n for n in names if n not in cex]
            if missing:
                print("[FAIL] %-18s UNSAFE 反例缺少输入 %s" % (name, missing))
                fails += 1
                continue
            # 反例值必须在声明的输入范围内
            out_of_range = [n for n in names if not (iv[n][0] <= cex[n] <= iv[n][1])]
            if out_of_range:
                print("[FAIL] %-18s UNSAFE 反例越界 %s（声明范围外）" % (name, out_of_range))
                fails += 1
                continue
            r = run_concrete(p, {n: cex[n] for n in names})
            if r[0] not in ("assert", "div"):
                print("[FAIL] %-18s UNSAFE 反例 %s 没有触发（执行结果 %s）" % (name, cex, r[0]))
                fails += 1
                continue
        print("[OK] %-18s %-6s" % (name, exp))

    print("=" * 60)
    total = len(PROGRAMS)
    print("共 %d 个程序，错 %d 个" % (total, fails))
    ok = (fails == 0)
    print("总结论：", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
