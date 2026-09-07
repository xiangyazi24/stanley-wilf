#!/usr/bin/env python3
"""Independent exact finite regression tests; these do NOT validate Lean code."""
from __future__ import annotations

import argparse
import itertools
import json
from functools import lru_cache
from pathlib import Path

Perm = tuple[int, ...]


def standardize(values: tuple[int, ...]) -> Perm:
    ranks = {value: i for i, value in enumerate(sorted(values))}
    return tuple(ranks[value] for value in values)


@lru_cache(maxsize=None)
def occurrences(perm: Perm, k: int) -> frozenset[Perm]:
    return frozenset(standardize(tuple(perm[i] for i in indices))
                     for indices in itertools.combinations(range(len(perm)), k))


def avoids(pattern: Perm, perm: Perm) -> bool:
    return pattern not in occurrences(perm, len(pattern))


def direct_sum(left: Perm, right: Perm) -> Perm:
    return left + tuple(len(left) + v for v in right)


def skew_sum(left: Perm, right: Perm) -> Perm:
    return tuple(len(right) + v for v in left) + right


def sum_cuts(perm: Perm) -> tuple[int, ...]:
    return tuple(k for k in range(1, len(perm)) if max(perm[:k]) < min(perm[k:]))


def skew_cuts(perm: Perm) -> tuple[int, ...]:
    return tuple(k for k in range(1, len(perm)) if min(perm[:k]) > max(perm[k:]))


def words_of_weight(n: int) -> tuple[tuple[int, ...], ...]:
    if n == 0:
        return ((),)
    return tuple((size,) + tail for size in (1, 2, 3) if size <= n
                 for tail in words_of_weight(n - size))


def run(max_n: int) -> dict[str, object]:
    if not 4 <= max_n <= 8:
        raise ValueError('max_n must be between 4 and 8 (factorial-size test space)')
    perms = {n: tuple(itertools.permutations(range(n))) for n in range(max_n + 1)}
    patterns = tuple(p for k in range(2, 5) for p in perms[k])
    cuts_checked = 0
    for group in perms.values():
        for perm in group:
            assert not (sum_cuts(perm) and skew_cuts(perm)), perm
            cuts_checked += 1

    # Every decomposition along ALL cuts reconstructs the permutation and
    # leaves indecomposable components. Check both possible operations.
    factorization_checks = 0
    for perm in (p for group in perms.values() for p in group):
        for cuts_fn, join in ((sum_cuts, direct_sum), (skew_cuts, skew_sum)):
            boundaries = (0,) + cuts_fn(perm) + (len(perm),)
            components = [standardize(perm[i:j]) for i, j in
                          zip(boundaries, boundaries[1:]) if i < j]
            result: Perm = ()
            for component in components:
                assert not cuts_fn(component)
                result = join(result, component)
            assert result == perm
            factorization_checks += 1

    # Constructor injectivity for every fixed pair of sizes, including zero.
    constructor_pairs = 0
    for m in range(max_n + 1):
        for n in range(max_n + 1 - m):
            for join in (direct_sum, skew_sum):
                seen: dict[Perm, tuple[Perm, Perm]] = {}
                for left, right in itertools.product(perms[m], perms[n]):
                    image = join(left, right)
                    assert image not in seen
                    seen[image] = (left, right)
                    assert sorted(image) == list(range(m + n))
                    constructor_pairs += 1

    # Pattern closure for ALL applicable orientations, not just one chosen case.
    closure_checks = 0
    for pattern in patterns:
        for cuts_fn, join in ((sum_cuts, direct_sum), (skew_cuts, skew_sum)):
            if cuts_fn(pattern):
                continue
            for m in range(max_n + 1):
                for n in range(max_n + 1 - m):
                    for left, right in itertools.product(perms[m], perms[n]):
                        if avoids(pattern, left) and avoids(pattern, right):
                            assert avoids(pattern, join(left, right)), (pattern, left, right)
                            closure_checks += 1

    count_inequalities = 0
    counts: dict[str, list[int]] = {}
    for pattern in patterns:
        a = [sum(avoids(pattern, perm) for perm in perms[n]) for n in range(max_n + 1)]
        assert a[0] == 1 and all(value > 0 for value in a)
        for m in range(max_n + 1):
            for n in range(max_n + 1 - m):
                assert a[m] * a[n] <= a[m+n]
                count_inequalities += 1
        for n in range(max_n + 1):
            for m in range(1, max_n + 1):
                assert a[m] ** (n // m) <= a[n]
        counts[''.join(str(i+1) for i in pattern)] = a
    # Exact degenerate case, not passed through a log-positive theorem.
    singleton_counts = [sum(avoids((0,), p) for p in perms[n]) for n in range(max_n + 1)]
    assert singleton_counts == [1] + [0] * max_n

    weighted_pairs = 0
    words = {n: words_of_weight(n) for n in range(9)}
    for m in range(9):
        for n in range(9-m):
            pairs = tuple(itertools.product(words[m], words[n]))
            assert len({left+right for left, right in pairs}) == len(pairs)
            weighted_pairs += len(pairs)
    # Required negative tests: the naive unrestricted/zero-weight versions fail.
    assert () + (1,) == (1,) + ()
    assert ((), (1,)) != ((1,), ())
    zero_weight = lambda word: sum(0 for _ in word)
    assert zero_weight(()) == zero_weight((0,))
    assert () + (0,) == (0,) + ()

    return {
        'max_permutation_size': max_n,
        'patterns_tested': len(patterns),
        'cut_dichotomy_permutations': cuts_checked,
        'factorizations_checked': factorization_checks,
        'constructor_input_pairs_checked': constructor_pairs,
        'avoidance_closure_checks': closure_checks,
        'count_supermultiplicativity_checks': count_inequalities,
        'positive_weight_sequence_pairs_checked': weighted_pairs,
        'singleton_pattern_counts': singleton_counts,
        'counts': counts,
        'all_python_assertions_passed': True,
        'lean_compilation_performed': False,
        'note': 'Independent exact finite tests, not a Lean/kernel verification certificate.',
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-n', type=int, default=7)
    parser.add_argument('--json', type=Path)
    args = parser.parse_args()
    result = run(args.max_n)
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(result, indent=2) + '\n')
    compact = {k: v for k, v in result.items() if k != 'counts'}
    print(json.dumps(compact, indent=2))


if __name__ == '__main__':
    main()
