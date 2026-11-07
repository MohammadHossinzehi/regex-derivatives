import itertools
import os
import random
import re
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
import regex_derivatives as rd  # noqa: E402
from regex_derivatives import Regex, RegexSyntaxError  # noqa: E402

ALPHA = "abc"


def all_strings(max_len, alphabet=ALPHA):
    for n in range(max_len + 1):
        for t in itertools.product(alphabet, repeat=n):
            yield "".join(t)


def random_pattern(rng, depth=4):
    """Random pattern in the syntax shared by this library and Python's re."""
    if depth == 0 or rng.random() < 0.25:
        return rng.choice(["a", "b", "c", "[ab]", "[^a]", ".", "[a-c]", "()"])
    k = rng.random()
    if k < 0.3:
        return random_pattern(rng, depth - 1) + random_pattern(rng, depth - 1)
    if k < 0.5:
        return "(" + random_pattern(rng, depth - 1) + "|" + random_pattern(rng, depth - 1) + ")"
    if k < 0.65:
        return "(" + random_pattern(rng, depth - 1) + ")*"
    if k < 0.75:
        return "(" + random_pattern(rng, depth - 1) + ")+"
    if k < 0.85:
        return "(" + random_pattern(rng, depth - 1) + ")?"
    lo = rng.randint(0, 2)
    hi = lo + rng.randint(0, 2)
    return "(" + random_pattern(rng, depth - 1) + "){%d,%d}" % (lo, hi)


def moore_minimize_size(d):
    """Independent minimiser (Moore's algorithm) used as an oracle for Hopcroft."""
    part = [1 if s in d.accepting else 0 for s in range(d.n_states)]
    while True:
        sig = {}
        new = []
        for s in range(d.n_states):
            key = (part[s], tuple(part[t] for t in d.trans[s]))
            new.append(sig.setdefault(key, len(sig)))
        if len(set(new)) == len(set(part)):
            return len(set(new))
        part = new


class OracleAgainstRe(unittest.TestCase):
    def test_random_patterns_vs_python_re(self):
        rng = random.Random(12345)
        strings = list(all_strings(6))
        for _ in range(150):
            pat = random_pattern(rng)
            rx = Regex(pat)
            ref = re.compile(pat, re.S)
            dfa = rx.minimal_dfa()
            for s in strings:
                want = ref.fullmatch(s) is not None
                self.assertEqual(rx.fullmatch(s), want, (pat, s))
                self.assertEqual(dfa.accepts(s), want, (pat, s))

    def test_hopcroft_matches_moore_and_is_idempotent(self):
        rng = random.Random(7)
        for _ in range(120):
            rx = Regex(random_pattern(rng))
            d, m = rx.dfa(), rx.minimal_dfa()
            self.assertEqual(m.n_states, moore_minimize_size(d))
            self.assertEqual(m.minimize().signature(), m.signature())
            self.assertLessEqual(m.n_states, d.n_states)


class BooleanOperators(unittest.TestCase):
    def test_intersection_and_complement_by_brute_force(self):
        rng = random.Random(99)
        strings = list(all_strings(5))
        for _ in range(60):
            p, q = random_pattern(rng, 3), random_pattern(rng, 3)
            both, nots = Regex(f"({p})&({q})"), Regex(f"~({p})")
            rp, rq = re.compile(p, re.S), re.compile(q, re.S)
            for s in strings:
                a, b = rp.fullmatch(s) is not None, rq.fullmatch(s) is not None
                self.assertEqual(both.accepts(s), a and b, (p, q, s))
                self.assertEqual(nots.accepts(s), not a, (p, s))

    def test_de_morgan_and_double_negation(self):
        rng = random.Random(3)
        for _ in range(40):
            p, q = random_pattern(rng, 3), random_pattern(rng, 3)
            self.assertTrue(Regex(f"~(({p})|({q}))").equivalent(Regex(f"~({p})&~({q})"))[0])
            self.assertTrue(Regex(f"~~({p})").equivalent(Regex(p))[0])

    def test_classic_identities(self):
        eq = lambda a, b: Regex(a).equivalent(Regex(b))[0]
        self.assertTrue(eq("(a|b)*", "(a*b*)*"))
        self.assertTrue(eq("(a*)*", "a*"))
        self.assertTrue(eq("a+", "aa*"))
        self.assertTrue(eq("(ab)*a", "a(ba)*"))
        self.assertTrue(eq("a{2,4}", "aa|aaa|aaaa"))
        self.assertFalse(eq("(ab)*", "a*b*"))
        self.assertTrue(eq("[]*", "()"))
        self.assertTrue(eq("~[]", ".*"))


class Decisions(unittest.TestCase):
    def test_witness_is_shortest_and_really_distinguishes(self):
        ok, w = Regex("a*b").equivalent(Regex("a*c"))
        self.assertFalse(ok)
        self.assertEqual(w, "b")
        self.assertTrue(Regex("(ab)*").equivalent(Regex("(ab)*(ab)?"))[0])
        ok, w = Regex("(ab)*").equivalent(Regex("(ab)*a?"))
        self.assertFalse(ok)
        self.assertEqual(w, "a")

    def test_subset(self):
        self.assertTrue(Regex("a+").subset_of(Regex("a*"))[0])
        ok, w = Regex("a*").subset_of(Regex("a+"))
        self.assertFalse(ok)
        self.assertEqual(w, "")

    def test_emptiness(self):
        self.assertTrue(Regex("a&b").is_empty())
        self.assertTrue(Regex(".*&~.*").is_empty())
        self.assertFalse(Regex("a*").is_empty())
        self.assertEqual(Regex("[0-9]{3}-[0-9]{4}").shortest(), "000-0000")

    def test_count_matches_brute_force(self):
        for pat in ["(a|b)*abb", "a*b*", "[ab]{2,3}", "~(.*aa.*)&[ab]*"]:
            rx = Regex(pat)
            for n in range(5):
                brute = sum(1 for s in all_strings(n, "ab") if len(s) == n and rx.fullmatch(s))
                restricted = Regex(f"({pat})&[ab]*")
                self.assertEqual(restricted.count(n), brute, (pat, n))

    def test_count_over_full_unicode(self):
        self.assertEqual(Regex(".").count(1), rd.MAXC + 1)
        self.assertEqual(Regex("[0-9]{3}").count(3), 1000)
        self.assertEqual(Regex("a*").count(7), 1)

    def test_enumerate_shortlex(self):
        self.assertEqual(Regex("(ab)*").examples(4), ["", "ab", "abab", "ababab"])
        self.assertEqual(Regex("[ab]{2}").examples(10, alphabet="ab"), ["aa", "ab", "ba", "bb"])
        self.assertEqual(Regex("a&b").examples(5), [])


class Searching(unittest.TestCase):
    def brute(self, rx, s, pos=0):
        for i in range(pos, len(s) + 1):
            for j in range(len(s), i - 1, -1):
                if rx.fullmatch(s[i:j]):
                    return (i, j)
        return None

    def test_leftmost_longest_vs_brute_force(self):
        rng = random.Random(5)
        for _ in range(80):
            rx = Regex(random_pattern(rng, 3))
            for s in ["", "a", "abc", "cabbac", "bbbb", "acbacb"]:
                self.assertEqual(rx.search(s), self.brute(rx, s), (rx.pattern, s))

    def test_findall(self):
        self.assertEqual(Regex("[0-9]+").findall("a12b345c6"), ["12", "345", "6"])
        self.assertEqual(Regex("ab*").findall("abbaab"), ["abb", "a", "ab"])

    def test_pathological_pattern_is_linear(self):
        rx = Regex("(a*)*b")
        self.assertFalse(rx.accepts("a" * 5000))
        self.assertTrue(rx.accepts("a" * 5000 + "b"))
        self.assertLessEqual(rx.minimal_dfa().n_states, 3)


class ParserAndPrinter(unittest.TestCase):
    def test_syntax_features(self):
        self.assertTrue(Regex(r"\d{3}-\d{4}").fullmatch("555-1234"))
        self.assertTrue(Regex(r"[\w.]+@\w+\.com").fullmatch("a.b@x.com"))
        self.assertTrue(Regex(r"[^\d\s]+").fullmatch("abc"))
        self.assertFalse(Regex(r"[^\d\s]+").fullmatch("ab c"))
        self.assertTrue(Regex(r"\x41\.").fullmatch("A."))
        self.assertTrue(Regex("café|naïve").fullmatch("naïve"))
        self.assertTrue(Regex("[a\\-z]+").fullmatch("a-z"))
        self.assertTrue(Regex("[a-]+").fullmatch("a-"))

    def test_unicode_beyond_bmp(self):
        self.assertTrue(Regex(".").fullmatch("\U0001F600"))
        self.assertTrue(Regex("[\U0001F600-\U0001F64F]+").fullmatch("\U0001F601\U0001F602"))

    def test_errors(self):
        for bad in ["(", ")", "(a", "[a", "*a", "a{", "a{2,1}", "\\", "[z-a]", "a{x}"]:
            with self.assertRaises(RegexSyntaxError, msg=bad):
                Regex(bad)

    def test_print_round_trip(self):
        rng = random.Random(21)
        for _ in range(100):
            rx = Regex(random_pattern(rng) + "&" + random_pattern(rng))
            again = Regex(rx.simplified)
            self.assertIs(again.node, rx.node, rx.pattern)

    def test_hash_consing_normalisation(self):
        self.assertIs(Regex("a|b").node, Regex("b|a|a").node)
        self.assertIs(Regex("[ab]").node, Regex("a|b").node)
        self.assertIs(Regex("(a*)*").node, Regex("a*").node)
        self.assertIs(Regex("a&.*").node, Regex("a").node)


class Cli(unittest.TestCase):
    def test_cli(self):
        import contextlib
        import io
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            self._run()

    def _run(self):
        self.assertEqual(rd.main(["match", "a+b", "aab"]), 0)
        self.assertEqual(rd.main(["match", "a+b", "b"]), 1)
        self.assertEqual(rd.main(["equiv", "(a|b)*", "(a*b*)*"]), 0)
        self.assertEqual(rd.main(["equiv", "a*", "a+"]), 1)
        self.assertEqual(rd.main(["subset", "a+", "a*"]), 0)
        self.assertEqual(rd.main(["dfa", "(a|b)*abb"]), 0)
        self.assertEqual(rd.main(["dfa", "a*", "--dot"]), 0)
        self.assertEqual(rd.main(["match", "(", "x"]), 2)


if __name__ == "__main__":
    unittest.main()
