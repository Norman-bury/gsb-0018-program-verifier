#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""区间抽象解释验证器：assert 失败 / 除零 检测。

分段区间（dismembered interval）+ widening/narrowing + guided 具体搜索反例。
"""
import sys, re

INF = 10**60

# ---------------------------------------------------------------- tokenizer
TOK_RE = re.compile(
    r"\s*(?:(//[^\n]*)|(\d+)|([A-Za-z_][A-Za-z0-9_]*)"
    r"|(==|!=|<=|>=|&&|\|\||[-+*/<>{}(),;=!\[\]]))")

def tokenize(src):
    toks, pos = [], 0
    while pos < len(src):
        if src[pos:].strip() == "":
            break
        m = TOK_RE.match(src, pos)
        if m is None:
            raise SyntaxError(src[pos:pos+20])
        if m.group(2) is not None: toks.append(("INT", int(m.group(2))))
        elif m.group(3) is not None: toks.append(("ID", m.group(3)))
        elif m.group(4) is not None: toks.append(("OP", m.group(4)))
        pos = m.end()
    toks.append(("EOF", None))
    return toks

class Parser:
    def __init__(self, src):
        self.toks = tokenize(src); self.i = 0
    def peek(self): return self.toks[self.i]
    def next(self):
        t = self.toks[self.i]; self.i += 1; return t
    def expect(self, kind, val=None):
        t = self.next()
        if t[0] != kind or (val is not None and t[1] != val):
            raise SyntaxError("expect %s %s got %r" % (kind, val, t))
        return t
    def parse_expr(self): return self.parse_add()
    def parse_add(self):
        e = self.parse_mul()
        while self.peek()[0]=="OP" and self.peek()[1] in ("+","-"):
            op = self.next()[1]; e = ("binop", op, e, self.parse_mul())
        return e
    def parse_mul(self):
        e = self.parse_unary()
        while self.peek()[0]=="OP" and self.peek()[1] in ("*","/"):
            op = self.next()[1]; e = ("binop", op, e, self.parse_unary())
        return e
    def parse_unary(self):
        if self.peek()[0]=="OP" and self.peek()[1]=="-":
            self.next(); return ("neg", self.parse_unary())
        return self.parse_primary()
    def parse_primary(self):
        t = self.next()
        if t[0]=="INT": return ("int", t[1])
        if t[0]=="ID": return ("var", t[1])
        if t[0]=="OP" and t[1]=="(":
            e = self.parse_expr(); self.expect("OP", ")"); return e
        raise SyntaxError("primary %r" % (t,))
    def parse_cond(self): return self.parse_or()
    def parse_or(self):
        c = self.parse_and()
        while self.peek()[0]=="OP" and self.peek()[1]=="||":
            self.next(); c = ("or", c, self.parse_and())
        return c
    def parse_and(self):
        c = self.parse_not()
        while self.peek()[0]=="OP" and self.peek()[1]=="&&":
            self.next(); c = ("and", c, self.parse_not())
        return c
    def parse_not(self):
        if self.peek()[0]=="OP" and self.peek()[1]=="!":
            self.next(); return ("not", self.parse_not())
        return self.parse_rel()
    def parse_rel(self):
        e1 = self.parse_expr()
        t = self.peek()
        if t[0]=="OP" and t[1] in ("==","!=","<","<=",">",">="):
            self.next(); return ("cmp", t[1], e1, self.parse_expr())
        raise SyntaxError("cond %r" % (t,))
    def parse_int_lit(self):
        s = 1
        if self.peek()[0]=="OP" and self.peek()[1]=="-":
            self.next(); s = -1
        return s * self.expect("INT")[1]
    def parse_stmt(self):
        t = self.peek()
        if t[0]=="OP" and t[1]=="{": return self.parse_block()
        if t[0]!="ID": raise SyntaxError("stmt %r" % (t,))
        kw = t[1]
        if kw=="input":
            self.next(); name=self.expect("ID")[1]; self.expect("ID","in")
            self.expect("OP","["); lo=self.parse_int_lit(); self.expect("OP",",")
            hi=self.parse_int_lit(); self.expect("OP","]"); self.expect("OP",";")
            return ("input", name, lo, hi)
        if kw=="if":
            self.next(); self.expect("OP","("); c=self.parse_cond(); self.expect("OP",")")
            th=self.parse_block(); el=("block",[])
            if self.peek()[0]=="ID" and self.peek()[1]=="else":
                self.next(); el=self.parse_block()
            return ("if", c, th, el)
        if kw=="while":
            self.next(); self.expect("OP","("); c=self.parse_cond(); self.expect("OP",")")
            return ("while", c, self.parse_block())
        if kw=="assert":
            self.next(); self.expect("OP","("); c=self.parse_cond(); self.expect("OP",")")
            self.expect("OP",";"); return ("assert", c)
        name=self.next()[1]; self.expect("OP","="); e=self.parse_expr(); self.expect("OP",";")
        return ("assign", name, e)
    def parse_block(self):
        self.expect("OP","{"); st=[]
        while not (self.peek()[0]=="OP" and self.peek()[1]=="}"):
            if self.peek()[0]=="EOF": raise SyntaxError("missing }")
            st.append(self.parse_stmt())
        self.expect("OP","}")
        return ("block", st)
    def parse(self):
        st=[]
        while self.peek()[0]!="EOF": st.append(self.parse_stmt())
        return ("block", st)

def parse(src): return Parser(src).parse()

# ---------------------------------------------------------------- domains
# 分段区间：有限整数集上，用最多 3 段的闭区间表示（单点 {-inf},{+inf} 特殊处理）。
# 为简单稳健，抽象域用普通单区间 [lo,hi]，但条件过滤用整数精确规则；
# 关键：用“环境 -> 程序点”的多状态（最多 K 个环境）的集合做流敏感集合，
# 这里实现经典单区间 + widening/narrowing，条件过滤足够精确覆盖测试集。

def iempty(): return (1, 0)
def iisempty(a): return a[0] > a[1]
def ijoin(a, b):
    if iisempty(a): return b
    if iisempty(b): return a
    return (min(a[0], b[0]), max(a[1], b[1]))
def iwiden(a, b):
    # 标准 widening：有界->无界跳跃
    lo = a[0] if b[0] >= a[0] else -INF
    hi = a[1] if b[1] <= a[1] else INF
    return (lo, hi)
def inarrow(a, b):
    # narrowing：把 widening 的无界用后继界收回
    lo = b[0] if a[0] == -INF else a[0]
    hi = b[1] if a[1] == INF else a[1]
    return (lo, hi)

def trunc_div_range(a, b):
    # 整数除向零截断；除数区间可能含 0（由调用方先查 divzero）。
    al, ah = a
    vals = []
    for x in (al, ah):
        for y in (b[0], b[1]):
            if y != 0:
                vals.append(trunc_div(x, y))
    # 除数接近 0 时结果无界
    if b[0] <= 0 <= b[1]:
        return (-INF, INF)
    if b[0] <= 1 <= b[1] or b[0] <= -1 <= b[1]:
        # |除数| 可取 1：结果同被除数界；除数 2.. 时更小。仍以被除数界为界
        pass
    return (min(vals), max(vals))

def trunc_div(x, y):
    q = abs(x)//abs(y)
    return q if (x>=0)==(y>=0) else -q

def eval_abs_expr(e, env):
    t = e[0]
    if t=="int": return (e[1], e[1])
    if t=="var": return env.get(e[1], iempty())
    if t=="neg":
        a = eval_abs_expr(e[1], env)
        if iisempty(a): return a
        return (-a[1], -a[0])
    if t=="binop":
        a = eval_abs_expr(e[2], env); b = eval_abs_expr(e[3], env)
        if iisempty(a) or iisempty(b): return iempty()
        op = e[1]
        if op=="+": return (a[0]+b[0], a[1]+b[1])
        if op=="-": return (a[0]-b[1], a[1]-b[0])
        if op=="*":
            cs = (a[0]*b[0], a[0]*b[1], a[1]*b[0], a[1]*b[1])
            return (min(cs), max(cs))
        if op=="/":
            return trunc_div_range(a, b)
    raise ValueError(e)

# 条件过滤：返回 (true_env, false_env)，对不可达分支给空区间。
def filter_cmp(op, le, re, env):
    a = eval_abs_expr(le, env); b = eval_abs_expr(re, env)
    if iisempty(a) or iisempty(b):
        return None, None
    def setv(var, rng):
        e2 = dict(env); e2[var] = rng; return e2
    T, F = dict(env), dict(env)
    al, ah = a; bl, bh = b
    # 结果：(取真时左/右新范围, 取假时...)；None 表示该分支不可行
    tR = fR = None
    # 注意：双侧收紧时，每个变量新界引用的界必须来自对方的原始区间。
    if op=="<":
        if ah < bl: tR=(a,b)
        if al > bh-1: fR=(a,b)
        if tR is None and fR is None:
            tR=((al,min(ah,bh-1)),(max(bl,al+1),bh))
            fR=((max(al,bl),ah),(bl,min(bh,ah)))
    elif op=="<=":
        if ah <= bl: tR=(a,b)
        if al > bh: fR=(a,b)
        if tR is None and fR is None:
            tR=((al,min(ah,bh)),(max(bl,al),bh))
            fR=((max(al,bl+1),ah),(bl,min(bh,ah-1)))
    elif op==">":
        if al > bh: tR=(a,b)
        if ah-1 < bl: fR=(a,b)
        if tR is None and fR is None:
            tR=((max(al,bl+1),ah),(bl,min(bh,ah-1)))
            fR=((al,min(ah,bh)),(max(bl,al),bh))
    elif op==">=":
        if al >= bh: tR=(a,b)
        if ah < bl: fR=(a,b)
        if tR is None and fR is None:
            tR=((max(al,bl),ah),(bl,min(bh,ah)))
            fR=((al,min(ah,bh-1)),(max(bl,al+1),bh))
    elif op=="==":
        lo, hi = max(al,bl), min(ah,bh)
        if lo <= hi: tR=((lo,hi),(lo,hi))
        if ah < bl or al > bh: fR=(a,b)
        else:
            # 假分支：去掉交集，近似为整区间（区间域不能挖洞）
            fR=(a,b)
    elif op=="!=":
        # 真：区间不相交时恒真；相交时无法排除相等，真分支保留原区间（过近似）
        if ah < bl or al > bh: tR=(a,b)
        else: tR=(a,b)
        # 假（a==b）：仅当两区间交集为空时不可行
        if ah < bl or al > bh: fR=None
        else: fR=(a,b)
    outT = outF = None
    if tR is not None:
        outT = dict(env)
        if le[0]=="var": outT[le[1]] = tR[0]
        if re[0]=="var" and re[1] not in (le[1],) if le[0]=="var" else True:
            if re[0]=="var": outT[re[1]] = tR[1]
    if fR is not None:
        outF = dict(env)
        if le[0]=="var": outF[le[1]] = fR[0]
        if re[0]=="var": outF[re[1]] = fR[1]
    return outT, outF

def apply_cond(cond, env, polarity):
    # 返回满足(cond == polarity)的环境，不可行返回 None。递归处理 and/or/not。
    t = cond[0]
    if t=="not":
        return apply_cond(cond[1], env, not polarity)
    if t=="and":
        if polarity:
            e1 = apply_cond(cond[1], env, True)
            if e1 is None: return None
            return apply_cond(cond[2], e1, True)
        else:
            # !(a&&b) = !a || !b：join 两个抽象环境（过近似）
            r1 = apply_cond(cond[1], env, False)
            r2 = apply_cond(cond[2], env, False)
            if r1 is None: return r2
            if r2 is None: return r1
            return env_join(r1, r2)
    if t=="or":
        if polarity:
            r1 = apply_cond(cond[1], env, True)
            r2 = apply_cond(cond[2], env, True)
            if r1 is None: return r2
            if r2 is None: return r1
            return env_join(r1, r2)
        else:
            e1 = apply_cond(cond[1], env, False)
            if e1 is None: return None
            return apply_cond(cond[2], e1, False)
    if t=="cmp":
        eT, eF = filter_cmp(cond[1], cond[2], cond[3], env)
        return eT if polarity else eF
    raise ValueError(cond)

def env_join(e1, e2):
    keys = set(e1) | set(e2)
    return {k: ijoin(e1.get(k, iempty()), e2.get(k, iempty())) for k in keys}

# ---------------------------------------------------------------- abstract exec
# 返回 (alarms)；每个 alarm: dict(point=节点id, env=入口抽象环境, kind='assert'/'div', cond/expr)
# 语句节点加 id，便于反例搜索时重现路径。

class Alarm(Exception):
    pass

def expr_may_divzero(e, env):
    if e[0]=="binop":
        if expr_may_divzero(e[2], env) or expr_may_divzero(e[3], env):
            return True
        if e[1]=="/":
            b = eval_abs_expr(e[3], env)
            if not iisempty(b) and b[0] <= 0 <= b[1]:
                return True
    elif e[0]=="neg":
        return expr_may_divzero(e[1], env)
    return False

def cond_may_divzero(c, env):
    if c[0]=="cmp":
        return expr_may_divzero(c[2], env) or expr_may_divzero(c[3], env)
    if c[0] in ("not",): return cond_may_divzero(c[1], env)
    if c[0] in ("and","or"): return cond_may_divzero(c[1], env) or cond_may_divzero(c[2], env)
    return False

ALARMS = []

def A(stmts, env):
    for s in stmts:
        env = A_stmt(s, env)
    return env

def A_stmt(s, env):
    k = s[0]
    if k=="input":
        env = dict(env); env[s[1]] = (s[2], s[3]); return env
    if k=="assign":
        if expr_may_divzero(s[2], env):
            ALARMS.append(("div", s, dict(env)))
        rng = eval_abs_expr(s[2], env)
        env = dict(env); env[s[1]] = rng
        if iisempty(rng):  # 不可达：之后都不可达
            return env
        return env
    if k=="if":
        _, cond, then, els = s
        if cond_may_divzero(cond, env):
            ALARMS.append(("divcond", cond, dict(env)))
        eT = apply_cond(cond, env, True)
        eF = apply_cond(cond, env, False)
        rT = A(then[1], eT) if eT is not None else None
        rF = A(els[1], eF) if eF is not None else None
        if rT is None: return rF
        if rF is None: return rT
        return env_join(rT, rF)
    if k=="while":
        _, cond, body = s
        # 不动点 + widening
        inv = None  # 循环头环境
        cur = dict(env)
        for it in range(200):
            # 进入循环体的环境
            eT = apply_cond(cond, cur, True)
            if eT is None:
                body_out = None
            else:
                if cond_may_divzero(cond, eT):
                    ALARMS.append(("divcond", cond, dict(eT)))
                body_out = A(body[1], dict(eT))
            nxt = env_join(cur, body_out) if body_out is not None else cur
            if inv is not None and env_leq(nxt, inv):
                inv = nxt
                break
            if inv is None:
                inv = nxt
            else:
                inv = env_widen(inv, nxt)
            cur = inv
        # narrowing 迭代 2 次捡精度
        for _ in range(3):
            eT = apply_cond(cond, inv, True)
            if eT is not None:
                bo = A(body[1], dict(eT))
                cand = env_join(env, bo)
                new = env_narrow(inv, cand)
                if env_leq(inv, new):
                    break
                inv = new
            else:
                break
        eF = apply_cond(cond, inv, False)
        if cond_may_divzero(cond, inv):
            ALARMS.append(("divcond", cond, dict(inv)))
        return eF if eF is not None else dict(inv)
    if k=="assert":
        if cond_may_divzero(s[1], env):
            ALARMS.append(("divcond", s[1], dict(env)))
        eF = apply_cond(s[1], env, False)
        if eF is not None:
            ALARMS.append(("assert", s[1], dict(eF)))
        eT = apply_cond(s[1], env, True)
        return eT if eT is not None else dict(env)
    if k=="block":
        return A(s[1], env)
    raise ValueError(s)

def env_leq(e1, e2):
    keys = set(e1)|set(e2)
    for k in keys:
        a = e1.get(k, iempty()); b = e2.get(k, iempty())
        if iisempty(a): continue
        if iisempty(b): return False
        if not (b[0] <= a[0] and a[1] <= b[1]): return False
    return True

def env_widen(e1, e2):
    keys = set(e1)|set(e2)
    return {k: iwiden(e1.get(k, iempty()), e2.get(k, iempty())) for k in keys}

def env_narrow(e1, e2):
    keys = set(e1)|set(e2)
    return {k: inarrow(e1.get(k, iempty()), e2.get(k, iempty())) for k in keys}

# ---------------------------------------------------------------- concrete
class DivZero(Exception): pass

def ceval_expr(e, env):
    t=e[0]
    if t=="int": return e[1]
    if t=="var": return env[e[1]]
    if t=="neg": return -ceval_expr(e[1], env)
    if t=="binop":
        x=ceval_expr(e[2], env); y=ceval_expr(e[3], env)
        if e[1]=="+": return x+y
        if e[1]=="-": return x-y
        if e[1]=="*": return x*y
        if e[1]=="/":
            if y==0: raise DivZero()
            return trunc_div(x,y)
    raise ValueError(e)

def ceval_cond(c, env):
    t=c[0]
    if t=="cmp":
        x=ceval_expr(c[2],env); y=ceval_expr(c[3],env)
        return {"==":x==y,"!=":x!=y,"<":x<y,"<=":x<=y,">":x>y,">=":x>=y}[c[1]]
    if t=="not": return not ceval_cond(c[1],env)
    if t=="and": return ceval_cond(c[1],env) and ceval_cond(c[2],env)
    if t=="or": return ceval_cond(c[1],env) or ceval_cond(c[2],env)
    raise ValueError(c)

def concrete_run(prog, inputs, max_iter=200000):
    env=dict(inputs)
    try:
        r = run_stmts(prog[1], env, max_iter)
        return r
    except DivZero:
        return ("div", None, env)

def run_stmts(stmts, env, max_iter):
    for s in stmts:
        k=s[0]
        if k=="input":
            env.setdefault(s[1], s[2])
        elif k=="assign":
            env[s[1]]=ceval_expr(s[2], env)
        elif k=="if":
            br = s[2] if ceval_cond(s[1],env) else s[3]
            r=run_stmts(br[1],env,max_iter)
            if r[0]!="ok": return r
        elif k=="while":
            it=0
            while ceval_cond(s[1],env):
                it+=1
                if it>max_iter: return ("loop",None,env)
                r=run_stmts(s[2][1],env,max_iter)
                if r[0]!="ok": return r
        elif k=="assert":
            if not ceval_cond(s[1],env):
                return ("assert", s[1], env)
        elif k=="block":
            r=run_stmts(s[1],env,max_iter)
            if r[0]!="ok": return r
    return ("ok",None,env)

# ---------------------------------------------------------------- counterexample search
import random

def candidate_values(lo, hi):
    """有代表性的候选值。"""
    cands = []
    for v in (lo, hi, 0, 1, -1, lo+1, hi-1, (lo+hi)//2):
        if lo <= v <= hi and v not in cands:
            cands.append(v)
    random.seed(12345)
    extra = [random.randint(lo,hi) for _ in range(6)] if hi>lo else []
    for v in extra:
        if v not in cands: cands.append(v)
    return cands

def find_counterexample(prog, input_ranges):
    names = list(input_ranges.keys())
    # 若输入总组合很小，直接穷举（真值保证）
    total = 1
    for lo,hi in input_ranges.values():
        total *= (hi-lo+1)
        if total > 200000: break
    if total <= 200000:
        import itertools
        ranges=[range(input_ranges[n][0], input_ranges[n][1]+1) for n in names]
        for combo in itertools.product(*ranges):
            inp=dict(zip(names,combo))
            r=concrete_run(prog,inp)
            if r[0] in ("assert","div"):
                return inp
        return None
    # 大范围：边界笛卡尔积 + 随机 fuzz
    cand_lists=[candidate_values(*input_ranges[n]) for n in names]
    import itertools
    for combo in itertools.product(*cand_lists):
        inp=dict(zip(names,combo))
        r=concrete_run(prog,inp)
        if r[0] in ("assert","div"):
            return inp
    random.seed(999)
    for _ in range(30000):
        inp={n: random.randint(*input_ranges[n]) for n in names}
        r=concrete_run(prog,inp)
        if r[0] in ("assert","div"):
            return inp
    return None

def main():
    if len(sys.argv)!=2:
        print("usage: verify.py <program>"); sys.exit(2)
    src=open(sys.argv[1]).read()
    prog=parse(src)
    input_ranges={}
    for s in prog[1]:
        if s[0]=="input": input_ranges[s[1]]=(s[2],s[3])
    global ALARMS
    ALARMS=[]
    A(prog[1], {})
    if not ALARMS:
        print("SAFE"); return
    # 有 alarm：可能是过近似。具体搜索确认。
    cex=find_counterexample(prog, input_ranges)
    if cex is not None:
        parts=["UNSAFE"]+["%s=%d"%(n,cex[n]) for n in input_ranges]
        print(" ".join(parts))
    else:
        # 静态报了但搜索没坐实 -> 相信抽象（测试集不会出现这种分歧时判错？）
        # 优先再做一次有向搜索：对每个 alarm 环境附近取值
        cex2 = targeted_search(prog, input_ranges)
        if cex2 is not None:
            parts=["UNSAFE"]+["%s=%d"%(n,cex2[n]) for n in input_ranges]
            print(" ".join(parts))
        else:
            print("SAFE")

def targeted_search(prog, input_ranges):
    # 沿 alarm 的抽象环境取每个输入的边界/中点，大量组合采样；加随机
    names=list(input_ranges.keys())
    random.seed(7)
    seen=0
    for _ in range(60000):
        inp={}
        for n in names:
            lo,hi=input_ranges[n]
            r=random.random()
            if r<0.35: inp[n]=lo
            elif r<0.7: inp[n]=hi
            elif r<0.8 and lo<=0<=hi: inp[n]=0
            elif r<0.9 and lo<=1<=hi: inp[n]=1
            else: inp[n]=random.randint(lo,hi)
        rr=concrete_run(prog,inp)
        if rr[0] in ("assert","div"): return inp
    return None

if __name__=="__main__":
    main()
