"""Regular expressions via Brzozowski derivatives, with intersection and complement.

Pure Python, zero dependencies.  The pipeline:

    pattern --parse--> hash-consed AST --derivatives--> DFA --Hopcroft--> minimal DFA

Because regexes are normalised modulo associativity, commutativity and
idempotence of alternation/intersection (plus a few more laws), the set of
derivatives of any regex is finite and the DFA construction terminates.
"""
from __future__ import annotations

import argparse
import sys
from bisect import bisect_right
from collections import deque

MAXC = 0x10FFFF

# ---------------------------------------------------------------------------
# Character sets as sorted, merged, inclusive code point ranges
# ---------------------------------------------------------------------------


def cs_norm(ranges):
    rs = sorted((lo, hi) for lo, hi in ranges if lo <= hi)
    out = []
    for lo, hi in rs:
        if out and lo <= out[-1][1] + 1:
            if hi > out[-1][1]:
                out[-1] = (out[-1][0], hi)
        else:
            out.append((lo, hi))
    return tuple(out)


def cs_complement(rs):
    out, prev = [], 0
    for lo, hi in rs:
        if lo > prev:
            out.append((prev, lo - 1))
        prev = hi + 1
    if prev <= MAXC:
        out.append((prev, MAXC))
    return tuple(out)


def cs_union(a, b):
    return cs_norm(a + b)


def cs_intersect(a, b):
    out, i, j = [], 0, 0
    while i < len(a) and j < len(b):
        lo, hi = max(a[i][0], b[j][0]), min(a[i][1], b[j][1])
        if lo <= hi:
            out.append((lo, hi))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return tuple(out)


def cs_contains(rs, c):
    i = bisect_right(rs, (c, MAXC + 1)) - 1
    return i >= 0 and rs[i][0] <= c <= rs[i][1]


# ---------------------------------------------------------------------------
# Hash-consed AST with smart constructors
# ---------------------------------------------------------------------------


class Node:
    __slots__ = ("kind", "args", "uid", "nullable")

    def __init__(self, kind, args, uid, nullable):
        self.kind, self.args, self.uid, self.nullable = kind, args, uid, nullable

    def __repr__(self):
        return f"<{to_str(self)}>"

    def __str__(self):
        return to_str(self)


_table: dict = {}


def _mk(kind, args, nullable):
    key = (kind, args)
    n = _table.get(key)
    if n is None:
        n = Node(kind, args, len(_table), nullable)
        _table[key] = n
    return n


EMPTY = _mk("empty", (), False)  # matches nothing
EPS = _mk("eps", (), True)  # matches only ""


def charset(ranges):
    rs = cs_norm(ranges)
    return EMPTY if not rs else _mk("set", (rs,), False)


def char(c):
    return charset([(ord(c), ord(c))])


ANY = charset([(0, MAXC)])


def cat(a, b):
    if a is EMPTY or b is EMPTY:
        return EMPTY
    if a is EPS:
        return b
    if b is EPS:
        return a
    if a.kind == "cat":  # right-associate
        return cat(a.args[0], cat(a.args[1], b))
    return _mk("cat", (a, b), a.nullable and b.nullable)


def cat_all(items):
    r = EPS
    for x in reversed(list(items)):
        r = cat(x, r)
    return r


def star(a):
    if a is EMPTY or a is EPS:
        return EPS
    if a.kind == "star":
        return a
    if a is ANY:
        return UNIVERSE
    return _mk("star", (a,), True)


def not_(a):
    if a.kind == "not":
        return a.args[0]
    return _mk("not", (a,), not a.nullable)


UNIVERSE = not_(EMPTY)  # Sigma*


def alt(items):
    flat, sets = {}, ()
    stack = list(items)
    while stack:
        x = stack.pop()
        if x.kind == "alt":
            stack.extend(x.args)
        elif x is EMPTY:
            continue
        elif x.kind == "set":
            sets = cs_union(sets, x.args[0])
        elif x is UNIVERSE:
            return UNIVERSE
        else:
            flat[x.uid] = x
    if sets:
        s = charset(sets)
        flat[s.uid] = s
    if not flat:
        return EMPTY
    if len(flat) == 1:
        return next(iter(flat.values()))
    args = tuple(flat[k] for k in sorted(flat))
    return _mk("alt", args, any(x.nullable for x in args))


def and_(items):
    flat, sets = {}, None
    stack = list(items)
    while stack:
        x = stack.pop()
        if x.kind == "and":
            stack.extend(x.args)
        elif x is EMPTY:
            return EMPTY
        elif x is UNIVERSE:
            continue
        elif x.kind == "set":
            sets = x.args[0] if sets is None else cs_intersect(sets, x.args[0])
        else:
            flat[x.uid] = x
    if sets is not None:
        s = charset(sets)
        if s is EMPTY:
            return EMPTY
        flat[s.uid] = s
    if not flat:
        return UNIVERSE
    if len(flat) == 1:
        return next(iter(flat.values()))
    args = tuple(flat[k] for k in sorted(flat))
    return _mk("and", args, all(x.nullable for x in args))


def opt(a):
    return alt([EPS, a])


def repeat(a, lo, hi=None):
    """a{lo,hi}; hi=None means unbounded."""
    if lo > 1000 or (hi is not None and (hi > 1000 or hi < lo)):
        raise ValueError("bad repetition bounds")
    head = cat_all([a] * lo)
    if hi is None:
        return cat(head, star(a))
    tail = EPS
    for _ in range(hi - lo):  # (a(a(a)?)?)? keeps the tree small
        tail = opt(cat(a, tail))
    return cat(head, tail)


def literal(s):
    return cat_all(char(c) for c in s)


# ---------------------------------------------------------------------------
# Derivatives
# ---------------------------------------------------------------------------

_dcache: dict = {}


def deriv(n: Node, c: int) -> Node:
    """Brzozowski derivative of n with respect to code point c."""
    key = (n.uid, c)
    r = _dcache.get(key)
    if r is not None:
        return r
    k = n.kind
    if k == "set":
        r = EPS if cs_contains(n.args[0], c) else EMPTY
    elif k in ("empty", "eps"):
        r = EMPTY
    elif k == "cat":
        a, b = n.args
        r = cat(deriv(a, c), b)
        if a.nullable:
            r = alt([r, deriv(b, c)])
    elif k == "alt":
        r = alt([deriv(x, c) for x in n.args])
    elif k == "and":
        r = and_([deriv(x, c) for x in n.args])
    elif k == "star":
        r = cat(deriv(n.args[0], c), n)
    elif k == "not":
        r = not_(deriv(n.args[0], c))
    else:  # pragma: no cover
        raise AssertionError(k)
    _dcache[key] = r
    return r


def matches(n: Node, s: str) -> bool:
    """Match by repeated differentiation, no automaton built."""
    for ch in s:
        n = deriv(n, ord(ch))
        if n is EMPTY:
            return False
    return n.nullable


def boundaries(n: Node) -> list:
    """Start points of the coarsest partition of code points that every
    character set inside n respects.  Derivatives never introduce new
    boundaries, so one partition serves the whole automaton."""
    pts, seen, stack = {0}, set(), [n]
    while stack:
        x = stack.pop()
        if x.uid in seen:
            continue
        seen.add(x.uid)
        if x.kind == "set":
            for lo, hi in x.args[0]:
                pts.add(lo)
                if hi < MAXC:
                    pts.add(hi + 1)
        elif x.kind in ("cat", "alt", "and", "star", "not"):
            stack.extend(x.args)
    return sorted(pts)


# ---------------------------------------------------------------------------
# DFA
# ---------------------------------------------------------------------------


class DFA:
    """Complete DFA over code points, compressed into character classes.

    bounds[i] is the first code point of class i; trans[s][i] is the target.
    """

    def __init__(self, bounds, trans, accepting, start=0, labels=None):
        self.bounds, self.trans, self.start = bounds, trans, start
        self.accepting = frozenset(accepting)
        self.labels = labels

    @property
    def n_states(self):
        return len(self.trans)

    def cls(self, c: int) -> int:
        return bisect_right(self.bounds, c) - 1

    def class_size(self, i: int) -> int:
        hi = self.bounds[i + 1] if i + 1 < len(self.bounds) else MAXC + 1
        return hi - self.bounds[i]

    def run(self, s: str):
        q = self.start
        for ch in s:
            q = self.trans[q][self.cls(ord(ch))]
        return q

    def accepts(self, s: str) -> bool:
        return self.run(s) in self.accepting

    def live_states(self):
        """States from which some accepting state is reachable."""
        rev = [[] for _ in self.trans]
        for s, row in enumerate(self.trans):
            for t in row:
                rev[t].append(s)
        live, stack = set(self.accepting), list(self.accepting)
        while stack:
            t = stack.pop()
            for s in rev[t]:
                if s not in live:
                    live.add(s)
                    stack.append(s)
        return live

    def minimize(self) -> "DFA":
        """Hopcroft's partition refinement, then canonical BFS renumbering."""
        n, k = self.n_states, len(self.bounds)
        inv = [[[] for _ in range(n)] for _ in range(k)]
        for s, row in enumerate(self.trans):
            for c, t in enumerate(row):
                inv[c][t].append(s)
        acc = frozenset(self.accepting)
        rest = set(range(n)) - acc
        blocks = [b for b in (set(acc), rest) if b]
        where = {}
        for i, b in enumerate(blocks):
            for s in b:
                where[s] = i
        work = deque(range(len(blocks)))
        inwork = set(work)
        while work:
            a = work.popleft()
            inwork.discard(a)
            splitter = list(blocks[a])
            for c in range(k):
                pre = set()
                for t in splitter:
                    pre.update(inv[c][t])
                touched = {}
                for s in pre:
                    touched.setdefault(where[s], set()).add(s)
                for bi, part in touched.items():
                    b = blocks[bi]
                    if len(part) == len(b):
                        continue
                    b -= part
                    blocks.append(part)
                    ni = len(blocks) - 1
                    for s in part:
                        where[s] = ni
                    if bi in inwork:
                        work.append(ni)
                        inwork.add(ni)
                    else:
                        pick = bi if len(b) <= len(part) else ni
                        work.append(pick)
                        inwork.add(pick)
        # canonical numbering: BFS from the start block in class order
        number, order = {where[self.start]: 0}, [where[self.start]]
        rep = {i: next(iter(b)) for i, b in enumerate(blocks)}
        qi = 0
        while qi < len(order):
            bi = order[qi]
            qi += 1
            for t in self.trans[rep[bi]]:
                tb = where[t]
                if tb not in number:
                    number[tb] = len(order)
                    order.append(tb)
        trans = [[number[where[t]] for t in self.trans[rep[bi]]] for bi in order]
        accepting = [number[bi] for bi in order if rep[bi] in acc]
        return DFA(list(self.bounds), trans, accepting, 0)

    def signature(self):
        return (tuple(self.bounds), tuple(map(tuple, self.trans)), tuple(sorted(self.accepting)))

    def is_empty(self):
        return not (self.live_states() & {self.start})

    def count(self, length: int) -> int:
        """Exact number of accepted strings of the given length over all code points."""
        vec = {self.start: 1}
        for _ in range(length):
            nxt = {}
            for s, w in vec.items():
                for i, t in enumerate(self.trans[s]):
                    nxt[t] = nxt.get(t, 0) + w * self.class_size(i)
            vec = nxt
        return sum(w for s, w in vec.items() if s in self.accepting)

    def enumerate(self, limit=20, alphabet=None, max_len=12):
        """Accepted strings in shortlex order, restricted to `alphabet`
        (default printable ASCII)."""
        chars = sorted(set(alphabet if alphabet is not None else map(chr, range(32, 127))))
        live = self.live_states()
        out, level = [], [("", self.start)]
        for length in range(max_len + 1):
            for text, q in level:
                if q in self.accepting:
                    out.append(text)
                    if len(out) >= limit:
                        return out
            nxt = []
            for text, q in level:
                for ch in chars:
                    t = self.trans[q][self.cls(ord(ch))]
                    if t in live:
                        nxt.append((text + ch, t))
            level = nxt
            if not level:
                break
        return out

    def find(self, s: str, pos=0):
        """Leftmost-longest match at or after pos: (start, end) or None."""
        live = self.live_states()
        for i in range(pos, len(s) + 1):
            q, last = self.start, (i if self.start in self.accepting else -1)
            if self.start not in live:
                return None
            for j in range(i, len(s)):
                q = self.trans[q][self.cls(ord(s[j]))]
                if q not in live:
                    break
                if q in self.accepting:
                    last = j + 1
            if last >= 0:
                return (i, last)
        return None

    def to_dot(self):
        lines = ["digraph dfa {", "  rankdir=LR;", '  __s [shape=point];', f"  __s -> q{self.start};"]
        for s in range(self.n_states):
            shape = "doublecircle" if s in self.accepting else "circle"
            lines.append(f"  q{s} [shape={shape}];")
        for s, row in enumerate(self.trans):
            grouped = {}
            for i, t in enumerate(row):
                lo = self.bounds[i]
                hi = (self.bounds[i + 1] - 1) if i + 1 < len(self.bounds) else MAXC
                grouped.setdefault(t, []).append((lo, hi))
            for t, rs in grouped.items():
                label = _fmt_set(cs_norm(rs)).replace('"', '\\"')
                lines.append(f'  q{s} -> q{t} [label="{label}"];')
        lines.append("}")
        return "\n".join(lines)


def build_dfa(n: Node, limit=100000) -> DFA:
    """Explore the derivative automaton of n (states are normalised regexes)."""
    bounds = boundaries(n)
    reps = bounds  # first code point of each class represents it
    index, states, trans = {n: 0}, [n], []
    i = 0
    while i < len(states):
        cur = states[i]
        row = []
        for c in reps:
            d = deriv(cur, c)
            j = index.get(d)
            if j is None:
                j = index[d] = len(states)
                states.append(d)
                if len(states) > limit:
                    raise RuntimeError("DFA state limit exceeded")
            row.append(j)
        trans.append(row)
        i += 1
    accepting = [k for k, st in enumerate(states) if st.nullable]
    return DFA(bounds, trans, accepting, 0, labels=states)


# ---------------------------------------------------------------------------
# Language level queries (all done on derivative automata)
# ---------------------------------------------------------------------------


def shortest_member(n: Node):
    """Shortest (then smallest) accepted string, or None if the language is empty."""
    bounds = boundaries(n)
    seen, queue = {n}, deque([(n, "")])
    while queue:
        cur, text = queue.popleft()
        if cur.nullable:
            return text
        for c in bounds:
            d = deriv(cur, c)
            if d is not EMPTY and d not in seen:
                seen.add(d)
                queue.append((d, text + chr(c)))
    return None


def equivalent(a: Node, b: Node):
    """(True, None) or (False, shortest string accepted by exactly one)."""
    diff = alt([and_([a, not_(b)]), and_([b, not_(a)])])
    w = shortest_member(diff)
    return (w is None, w)


def subset(a: Node, b: Node):
    """(True, None) if L(a) is a subset of L(b), else (False, counterexample)."""
    w = shortest_member(and_([a, not_(b)]))
    return (w is None, w)


# ---------------------------------------------------------------------------
# Printing
# ---------------------------------------------------------------------------

_META = set("\\.[]()|&~*+?{}^-")


def _esc(c):
    if c in _META:
        return "\\" + c
    o = ord(c)
    if c == "\n":
        return "\\n"
    if c == "\t":
        return "\\t"
    if c == "\r":
        return "\\r"
    if o < 32 or o == 127:
        return f"\\x{o:02x}"
    return c


def _fmt_set(rs):
    if rs == ((0, MAXC),):
        return "."
    if len(rs) == 1 and rs[0][0] == rs[0][1]:
        return _esc(chr(rs[0][0]))
    neg = False
    if sum(hi - lo + 1 for lo, hi in rs) > (MAXC + 1) // 2:
        rs, neg = cs_complement(rs), True
    parts = []
    for lo, hi in rs:
        if lo == hi:
            parts.append(_esc(chr(lo)))
        elif hi == lo + 1:
            parts.append(_esc(chr(lo)) + _esc(chr(hi)))
        else:
            parts.append(_esc(chr(lo)) + "-" + _esc(chr(hi)))
    return "[" + ("^" if neg else "") + "".join(parts) + "]"


def to_str(n: Node, level=0) -> str:
    k = n.kind
    if k == "empty":
        return "[]"
    if k == "eps":
        return "()"
    if k == "set":
        return _fmt_set(n.args[0])
    if k == "star":
        c = n.args[0]
        return (to_str(c) if c.kind == "set" else "(" + to_str(c) + ")") + "*"
    if k == "not":
        c = n.args[0]
        return "~" + (to_str(c) if c.kind == "set" else "(" + to_str(c) + ")")
    if k == "cat":
        s = "".join(to_str(x, 2) for x in n.args)
        return "(" + s + ")" if level > 2 else s
    if k == "and":
        s = "&".join(to_str(x, 2) for x in n.args)
        return "(" + s + ")" if level > 1 else s
    if k == "alt":
        s = "|".join(to_str(x, 1) for x in n.args)
        return "(" + s + ")" if level > 0 else s
    raise AssertionError(k)  # pragma: no cover


# ---------------------------------------------------------------------------
# Parser
# ---------------------------------------------------------------------------


class RegexSyntaxError(ValueError):
    pass


_DIGIT = [(48, 57)]
_WORD = [(48, 57), (65, 90), (95, 95), (97, 122)]
_SPACE = [(9, 13), (32, 32)]
_ESCAPES = {"n": "\n", "t": "\t", "r": "\r", "f": "\f", "v": "\v", "0": "\0"}
_CLASS_ESC = {
    "d": _DIGIT, "w": _WORD, "s": _SPACE,
    "D": cs_complement(cs_norm(_DIGIT)), "W": cs_complement(cs_norm(_WORD)),
    "S": cs_complement(cs_norm(_SPACE)),
}


class _Parser:
    """alt := inter ('|' inter)* ; inter := cat ('&' cat)* ; cat := rep*
    rep := '~' rep | atom postfix* ; postfix := * + ? {m} {m,} {m,n}"""

    def __init__(self, text):
        self.s, self.i = text, 0

    def err(self, msg):
        raise RegexSyntaxError(f"{msg} at position {self.i} in {self.s!r}")

    def peek(self):
        return self.s[self.i] if self.i < len(self.s) else None

    def parse(self):
        n = self.alt()
        if self.peek() is not None:
            self.err(f"unexpected {self.peek()!r}")
        return n

    def alt(self):
        parts = [self.inter()]
        while self.peek() == "|":
            self.i += 1
            parts.append(self.inter())
        return alt(parts)

    def inter(self):
        parts = [self.cat()]
        while self.peek() == "&":
            self.i += 1
            parts.append(self.cat())
        return and_(parts)

    def cat(self):
        parts = []
        while self.peek() is not None and self.peek() not in "|&)":
            parts.append(self.rep())
        return cat_all(parts)

    def rep(self):
        if self.peek() == "~":
            self.i += 1
            return not_(self.rep())
        a = self.atom()
        while True:
            c = self.peek()
            if c == "*":
                self.i += 1
                a = star(a)
            elif c == "+":
                self.i += 1
                a = cat(a, star(a))
            elif c == "?":
                self.i += 1
                a = opt(a)
            elif c == "{":
                a = self.braces(a)
            else:
                return a

    def number(self):
        j = self.i
        while self.peek() is not None and self.peek().isdigit():
            self.i += 1
        return int(self.s[j:self.i]) if j != self.i else None

    def braces(self, a):
        self.i += 1
        lo = self.number()
        if lo is None:
            self.err("expected a number after '{'")
        hi = lo
        if self.peek() == ",":
            self.i += 1
            hi = self.number()
        if self.peek() != "}":
            self.err("expected '}'")
        self.i += 1
        try:
            return repeat(a, lo, hi)
        except ValueError as e:
            self.err(str(e))

    def escape(self):
        self.i += 1
        c = self.peek()
        if c is None:
            self.err("dangling backslash")
        self.i += 1
        if c == "x":
            hexs = self.s[self.i:self.i + 2]
            try:
                v = int(hexs, 16)
            except ValueError:
                self.err("bad \\x escape")
            self.i += 2
            return ("char", v)
        if c in _CLASS_ESC:
            return ("set", _CLASS_ESC[c])
        return ("char", ord(_ESCAPES.get(c, c)))

    def atom(self):
        c = self.peek()
        if c == "(":
            self.i += 1
            n = self.alt()
            if self.peek() != ")":
                self.err("missing ')'")
            self.i += 1
            return n
        if c == "[":
            return self.klass()
        if c == ".":
            self.i += 1
            return ANY
        if c in "*+?{":
            self.err(f"nothing to repeat before {c!r}")
        if c == "\\":
            kind, v = self.escape()
            return charset([(v, v)]) if kind == "char" else charset(v)
        self.i += 1
        return char(c)

    def klass(self):
        self.i += 1
        neg = False
        if self.peek() == "^":
            neg = True
            self.i += 1
        ranges = []
        while True:
            c = self.peek()
            if c is None:
                self.err("missing ']'")
            if c == "]":
                self.i += 1
                break
            lo = self.class_item()
            if lo[0] == "set":
                ranges.extend(lo[1])
                continue
            if self.peek() == "-" and self.s[self.i + 1:self.i + 2] not in ("]", ""):
                self.i += 1
                hi = self.class_item()
                if hi[0] != "char" or hi[1] < lo[1]:
                    self.err("bad range")
                ranges.append((lo[1], hi[1]))
            else:
                ranges.append((lo[1], lo[1]))
        rs = cs_norm(ranges)
        return charset(cs_complement(rs) if neg else rs)

    def class_item(self):
        if self.peek() == "\\":
            return self.escape()
        c = self.peek()
        self.i += 1
        return ("char", ord(c))


def parse(pattern: str) -> Node:
    return _Parser(pattern).parse()


# ---------------------------------------------------------------------------
# Friendly wrapper
# ---------------------------------------------------------------------------


class Regex:
    def __init__(self, pattern: str):
        self.pattern = pattern
        self.node = parse(pattern)
        self._dfa = None
        self._min = None

    def __repr__(self):
        return f"Regex({self.pattern!r})"

    @property
    def simplified(self):
        return to_str(self.node)

    def fullmatch(self, s: str) -> bool:
        """Match by differentiation (no automaton)."""
        return matches(self.node, s)

    def dfa(self) -> DFA:
        if self._dfa is None:
            self._dfa = build_dfa(self.node)
        return self._dfa

    def minimal_dfa(self) -> DFA:
        if self._min is None:
            self._min = self.dfa().minimize()
        return self._min

    def accepts(self, s: str) -> bool:
        return self.minimal_dfa().accepts(s)

    def search(self, s: str, pos=0):
        return self.minimal_dfa().find(s, pos)

    def findall(self, s: str):
        out, pos = [], 0
        while pos <= len(s):
            m = self.search(s, pos)
            if m is None:
                break
            out.append(s[m[0]:m[1]])
            pos = m[1] if m[1] > m[0] else m[1] + 1
        return out

    def is_empty(self):
        return shortest_member(self.node) is None

    def shortest(self):
        return shortest_member(self.node)

    def equivalent(self, other: "Regex"):
        return equivalent(self.node, other.node)

    def subset_of(self, other: "Regex"):
        return subset(self.node, other.node)

    def count(self, length: int) -> int:
        return self.minimal_dfa().count(length)

    def examples(self, limit=10, alphabet=None, max_len=12):
        return self.minimal_dfa().enumerate(limit, alphabet, max_len)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main(argv=None):
    p = argparse.ArgumentParser(prog="regex_derivatives", description=__doc__.split("\n")[0])
    sub = p.add_subparsers(dest="cmd", required=True)
    a = sub.add_parser("match", help="full match a string"); a.add_argument("pattern"); a.add_argument("text")
    a = sub.add_parser("search", help="leftmost-longest search"); a.add_argument("pattern"); a.add_argument("text")
    a = sub.add_parser("equiv", help="decide equivalence, print a witness if different"); a.add_argument("p1"); a.add_argument("p2")
    a = sub.add_parser("subset", help="is L(p1) a subset of L(p2)?"); a.add_argument("p1"); a.add_argument("p2")
    a = sub.add_parser("dfa", help="state counts and optional DOT output"); a.add_argument("pattern"); a.add_argument("--dot", action="store_true")
    a = sub.add_parser("enum", help="shortlex example strings"); a.add_argument("pattern"); a.add_argument("-n", type=int, default=10); a.add_argument("--alphabet")
    a = sub.add_parser("count", help="count accepted strings of a given length over ALL code points"); a.add_argument("pattern"); a.add_argument("length", type=int)
    args = p.parse_args(argv)
    try:
        if args.cmd == "match":
            ok = Regex(args.pattern).fullmatch(args.text)
            print("match" if ok else "no match")
            return 0 if ok else 1
        if args.cmd == "search":
            m = Regex(args.pattern).search(args.text)
            print("no match" if m is None else f"{m[0]}:{m[1]} {args.text[m[0]:m[1]]!r}")
            return 1 if m is None else 0
        if args.cmd in ("equiv", "subset"):
            r1, r2 = Regex(args.p1), Regex(args.p2)
            ok, w = r1.equivalent(r2) if args.cmd == "equiv" else r1.subset_of(r2)
            if ok:
                print("equivalent" if args.cmd == "equiv" else "subset")
                return 0
            print(f"not {'equivalent' if args.cmd == 'equiv' else 'a subset'}; witness: {w!r}")
            return 1
        if args.cmd == "dfa":
            r = Regex(args.pattern)
            d, m = r.dfa(), r.minimal_dfa()
            if args.dot:
                print(m.to_dot())
            else:
                print(f"simplified: {r.simplified}")
                print(f"derivative DFA: {d.n_states} states, minimal: {m.n_states} states, {len(m.bounds)} character classes")
            return 0
        if args.cmd == "enum":
            for s in Regex(args.pattern).examples(args.n, args.alphabet):
                print(repr(s))
            return 0
        if args.cmd == "count":
            print(Regex(args.pattern).count(args.length))
            return 0
    except RegexSyntaxError as e:
        print(f"syntax error: {e}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
