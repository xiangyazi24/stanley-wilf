#!/usr/bin/env python3
"""Exhaustive small-model checks for Positions/Closure; NOT Lean verification."""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

from test_small_cases import (
    avoids, direct_sum, skew_sum, standardize, sum_cuts, skew_cuts,
)


def selections(n: int):
    for k in range(n + 1):
        yield from itertools.combinations(range(n), k)


def run(max_n: int = 6) -> dict[str, object]:
    if not 1 <= max_n <= 7:
        raise ValueError('max_n must be in [1,7] (exhaustive factorial search)')
    positions_checked = 0
    # Include a boundary beyond the codomain and the empty-domain cases.
    for n in range(10):
        for e in selections(n):
            for boundary in range(n + 2):
                if all(x < boundary for x in e):
                    assert tuple(e) == tuple(x for x in e if x < boundary)
                elif all(boundary <= x for x in e):
                    restricted = tuple(x - boundary for x in e)
                    assert all(x >= 0 for x in restricted)
                    assert all(x < y for x, y in zip(restricted, restricted[1:]))
                else:
                    cut = next(i for i, x in enumerate(e) if boundary <= x)
                    assert 0 < cut < len(e)
                    assert all((x < boundary) == (i < cut) for i, x in enumerate(e))
                positions_checked += 1

    permutations = {n: tuple(itertools.permutations(range(n)))
                    for n in range(max_n + 1)}
    block_pairs = 0
    occurrence_checks = 0
    crossing_checks = 0
    for m in range(max_n + 1):
        for n in range(max_n + 1 - m):
            embeddings = tuple(selections(m + n))
            for left, right in itertools.product(permutations[m], permutations[n]):
                for join, cuts in ((direct_sum, sum_cuts), (skew_sum, skew_cuts)):
                    perm = join(left, right)
                    block_pairs += 1
                    for i in range(m):
                        expected = left[i] if join is direct_sum else n + left[i]
                        assert perm[i] == expected
                    for j in range(n):
                        expected = m + right[j] if join is direct_sum else right[j]
                        assert perm[m + j] == expected
                    for e in embeddings:
                        pattern = standardize(tuple(perm[i] for i in e))
                        if all(i < m for i in e):
                            assert pattern == standardize(tuple(left[i] for i in e))
                        elif all(m <= i for i in e):
                            assert pattern == standardize(tuple(right[i-m] for i in e))
                        else:
                            cut = next(i for i, x in enumerate(e) if m <= x)
                            assert cut in cuts(pattern), (left, right, e, pattern)
                            assert all((x < m) == (i < cut) for i, x in enumerate(e))
                            crossing_checks += 1
                        occurrence_checks += 1

    # Dropping indecomposability would make either closure theorem false.
    singleton = (0,)
    assert avoids((0, 1), singleton)
    assert not avoids((0, 1), direct_sum(singleton, singleton))
    assert avoids((1, 0), singleton)
    assert not avoids((1, 0), skew_sum(singleton, singleton))
    # The empty pattern is contained even in the empty permutation.
    assert all(not avoids((), p) for group in permutations.values() for p in group)

    return {
        'max_block_sum_size': max_n,
        'position_selections_with_boundaries': positions_checked,
        'block_constructor_pairs': block_pairs,
        'individual_occurrences_checked': occurrence_checks,
        'crossing_occurrences_with_explicit_cut': crossing_checks,
        'missing_indecomposability_counterexamples_checked': 2,
        'empty_blocks_and_empty_patterns_included': True,
        'all_python_assertions_passed': True,
        'lean_compilation_performed': False,
        'note': 'Independent executable models, not proof of Lean elaboration or kernel checking.',
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-n', type=int, default=6)
    parser.add_argument('--json', type=Path)
    args = parser.parse_args()
    result = run(args.max_n)
    rendered = json.dumps(result, indent=2) + '\n'
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(rendered)
    print(rendered, end='')


if __name__ == '__main__':
    main()
