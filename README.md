# regex-derivatives

A regular expression engine built on **Brzozowski derivatives**, in pure Python with zero dependencies. Besides the usual operators it supports **intersection (`&`) and complement (`~`)**, which makes it possible to decide things most regex engines cannot: whether two patterns describe the same language, whether one contains the other, and what the shortest string separating them is.

## Why this is interesting

The derivative of a language L by a character c is the set of suffixes w such that cw is in L. Differentiating a regex by each input character and checking whether the result accepts the empty string is a complete matcher in a few lines. The same idea builds a DFA: states are the (normalised) regexes reachable by differentiation. Because intersection and complement are just more node types with their own derivative rules, extended regexes come for free, with no NFA blow-up and no backtracking.

Pipeline: `pattern -> parser -> hash-consed AST -> derivative DFA -> Hopcroft minimisation`.

## Features

- Syntax: literals, `.`, classes `[a-z\d_]`, `[^...]`, escapes (`\d \w \s \D \W \S \n \t \xHH`), groups, `|`, `*`, `+`, `?`, `{m}`, `{m,}`, `{m,n}`, plus `&` and `~`.
- Full Unicode: character sets are interval lists over code points and the DFA works on character classes, so `.` costs one class, not 1.1 million edges.
- Matching by differentiation (no automaton) or via the minimal DFA. Matching time is linear in the input, so patterns like `(a*)*b` are not catastrophic.
- Leftmost-longest `search` and `findall`.
- Language level decisions: `equivalent` and `subset_of` (with a shortest counterexample), `is_empty`, `shortest`.
- Exact counting of accepted strings of a given length over the whole Unicode alphabet, and shortlex enumeration of members.
- Canonically numbered minimal DFAs, Graphviz DOT export, and a CLI.

## Usage

Requires Python 3.9+.

```python
from regex_derivatives import Regex

Regex(r"(a|b)*abb").fullmatch("babb")          # True
Regex(r"\d+").search("ab123cd")                # (2, 5)
Regex(r"(a|b)*").equivalent(Regex(r"(a*b*)*")) # (True, None)
Regex(r"a*b").equivalent(Regex(r"a*c"))        # (False, 'b')

# Strings over [a-c] that contain no 'b':
Regex(r"[a-c]+&~(.*b.*)").examples(5)          # ['a', 'c', 'aa', 'ac', 'ca']
Regex(r"[0-9]{3}").count(3)                    # 1000
```

Command line:

```
python regex_derivatives.py match '(a|b)*abb' aabb
python regex_derivatives.py equiv '(a|b)*' '(a*b*)*'
python regex_derivatives.py subset 'a+' 'a*'
python regex_derivatives.py enum '[ab]*abb' -n 5
python regex_derivatives.py count '[0-9]{3}' 3
python regex_derivatives.py dfa '(a|b)*abb' --dot > dfa.dot
```

Syntax notes: `~` binds to the following repetition-level item (`~a*` means `~(a*)`), `&` binds looser than concatenation and tighter than `|`. `[]` is the empty language and `()` is the empty string.

## Design decisions

- **Hash-consing plus smart constructors.** Every node is interned, so equality is pointer equality, and constructors normalise modulo associativity, commutativity and idempotence of `|` and `&`, `r**=r`, `~~r=r`, merging of character sets, and the unit/zero laws. This is what guarantees a finite set of derivatives and keeps the DFA small (the derivative DFA is often already minimal).
- **One partition for the whole automaton.** Derivatives never create new character set boundaries, so the boundaries of the original pattern define the classes for every state.
- **Equivalence by emptiness.** `L(a) = L(b)` iff `(a & ~b) | (b & ~a)` is empty; a breadth first search over derivatives finds the shortest witness.
- **Hopcroft minimisation** with a canonical BFS renumbering, so equal languages give identical transition tables.

## Testing

```
python -m unittest -v
```

The suite uses independent oracles instead of hand written examples only: random patterns are checked against Python's `re` on every string up to length 6, Hopcroft's state counts are checked against a separate Moore implementation, extended operators and counting are checked by brute force, `search` is checked against a brute force leftmost-longest scan, and the printer is checked to round trip to the identical interned node.
