#!/usr/bin/env python3
"""Exact independent models of the new first-component route, not Lean checking.

The tests exercise both inverses of the variable-cut first-factor bijection,
not merely a equality of counts. Prefix restrictions use the actual values,
so a mistaken standardization or suffix offset is detectable.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
from test_small_cases import Perm, avoids, direct_sum, skew_sum, sum_cuts, skew_cuts


def complement(perm: Perm) -> Perm:
    return tuple(len(perm) - 1 - value for value in perm)


def boundaries(perm: Perm) -> tuple[int, ...]:
    return tuple(c for c in range(len(perm) + 1)
                 if all(value < c for value in perm[:c]))


def direct_first(perm: Perm) -> tuple[int, Perm, Perm]:
    if not perm:
        raise ValueError('the empty object has no positive first component')
    c = min(c for c in boundaries(perm) if c > 0)
    return c, perm[:c], tuple(v - c for v in perm[c:])


def skew_first(perm: Perm) -> tuple[int, Perm, Perm]:
    c, left, right = direct_first(complement(perm))
    return c, complement(left), complement(right)


def is_perm(values: Perm) -> bool:
    return sorted(values) == list(range(len(values)))


def run(max_n: int, avoider_max_n: int) -> dict[str, object]:
    if not 4 <= max_n <= 8 or not 4 <= avoider_max_n <= min(7, max_n):
        raise ValueError('require 4 <= avoider_max_n <= min(7, max_n), max_n <= 8')
    perms = {n: tuple(itertools.permutations(range(n))) for n in range(max_n + 1)}
    modes = ((sum_cuts, direct_sum, direct_first), (skew_cuts, skew_sum, skew_first))
    checked = dict(boundary_equivalences=0, actual_block_reconstructions=0,
                   unique_positive_first_factors=0, complement_cut_checks=0,
                   complement_constructor_checks=0, complement_avoidance_equivalences=0,
                   variable_cut_bijection_pairs=0,
                   avoiding_first_factors=0, avoiding_constructor_pairs=0,
                   coefficient_recurrences=0, convolution_supermultiplicativity=0,
                   abstract_convolution_sequences=0, abstract_convolution_checks=0)

    # Every cut, including zero and the full length. These are actual restrictions.
    for group in perms.values():
        for perm in group:
            n = len(perm)
            bs = boundaries(perm)
            assert bs == tuple(sorted(set((0,) + sum_cuts(perm) + (n,))))
            for c in range(n + 1):
                invariant = c in bs
                assert invariant == (set(perm[:c]) == set(range(c)))
                if invariant:
                    assert all((perm[i] < c) == (i < c) for i in range(n))
                    left, right = perm[:c], tuple(v - c for v in perm[c:])
                    assert is_perm(left) and is_perm(right)
                    assert direct_sum(left, right) == perm
                    for d in range(c + 1):
                        assert (d in boundaries(left)) == (d in bs)
                    checked['actual_block_reconstructions'] += 1
                checked['boundary_equivalences'] += 1
            assert complement(complement(perm)) == perm
            assert sum_cuts(complement(perm)) == skew_cuts(perm)
            assert skew_cuts(complement(perm)) == sum_cuts(perm)
            checked['complement_cut_checks'] += 1
            if n:
                for cuts_fn, join, split in modes:
                    c, left, right = split(perm)
                    assert 0 < c <= n and len(left) == c and len(right) == n-c
                    assert is_perm(left) and is_perm(right) and not cuts_fn(left)
                    assert join(left, right) == perm
                    candidates = []
                    for candidate in cuts_fn(perm) + (n,):
                        if join is direct_sum:
                            a = perm[:candidate]
                        else:
                            a = tuple(v - (n-candidate) for v in perm[:candidate])
                        if not cuts_fn(a):
                            candidates.append(candidate)
                    assert candidates == [c]
                    checked['unique_positive_first_factors'] += 1

    # Complement identity for the exact constructor, including empty blocks.
    for m in range(max_n + 1):
        for n in range(max_n + 1-m):
            for a, b in itertools.product(perms[m], perms[n]):
                assert complement(direct_sum(a, b)) == skew_sum(complement(a), complement(b))
                checked['complement_constructor_checks'] += 1

    # The cut varies across the whole domain: this is stronger than fixed-cut injectivity.
    for n in range(1, max_n + 1):
        for cuts_fn, join, split in modes:
            images: dict[Perm, tuple[int, Perm, Perm]] = {}
            for c in range(1, n+1):
                for a, b in itertools.product(perms[c], perms[n-c]):
                    if cuts_fn(a):
                        continue
                    image = join(a, b)
                    triple = c, a, b
                    assert image not in images, ('variable-cut collision', images.get(image), triple)
                    images[image] = triple
                    assert split(image) == triple
                    checked['variable_cut_bijection_pairs'] += 1
            assert set(images) == set(perms[n])

    # Genuine avoidance classes, both admissible orientations, not just one.
    patterns = ((0,),) + tuple(p for k in range(2, 5) for p in perms[k])
    orientations = 0
    for pattern in patterns:
        for n in range(avoider_max_n + 1):
            for p in perms[n]:
                assert avoids(pattern, p) == avoids(complement(pattern), complement(p))
                checked['complement_avoidance_equivalences'] += 1
        av = {n: tuple(p for p in perms[n] if avoids(pattern, p))
              for n in range(avoider_max_n + 1)}
        for cuts_fn, join, split in modes:
            if cuts_fn(pattern):
                continue
            orientations += 1
            atoms = {n: tuple(p for p in av[n] if n > 0 and not cuts_fn(p))
                     for n in av}
            a = [len(av[n]) for n in av]
            i = [len(atoms[n]) for n in atoms]
            assert a[0] == 1 and i[0] == 0
            for n in range(1, avoider_max_n + 1):
                images: set[Perm] = set()
                for c in range(1, n+1):
                    for left, right in itertools.product(atoms[c], av[n-c]):
                        image = join(left, right)
                        assert avoids(pattern, image)
                        assert image not in images
                        images.add(image)
                        assert split(image) == (c, left, right)
                        checked['avoiding_constructor_pairs'] += 1
                assert images == set(av[n])
                for p in av[n]:
                    c, left, right = split(p)
                    assert left in atoms[c] and right in av[n-c]
                    if join is skew_sum:
                        assert complement(left) == direct_first(complement(p))[1]
                    checked['avoiding_first_factors'] += 1
            for n in range(avoider_max_n + 1):
                assert a[n] == (int(n == 0) + sum(i[j] * a[n-j] for j in range(1, n+1)))
                checked['coefficient_recurrences'] += 1
            for m in range(avoider_max_n + 1):
                for n in range(avoider_max_n + 1-m):
                    partial = a[n] if m == 0 else sum(i[j] * a[m+n-j] for j in range(1, m+1))
                    assert a[m] * a[n] <= partial <= a[m+n]
                    checked['convolution_supermultiplicativity'] += 1

    # The new convolution lemma needs no positivity at each positive size.
    # Check sparse/periodic atoms as well as ordinary aperiodic classes.
    horizon = 12
    for atom_prefix in itertools.product(range(3), repeat=6):
        i = (0,) + atom_prefix + (0,) * (horizon-6)
        a = [1]
        for n in range(1, horizon+1):
            a.append(sum(i[j] * a[n-j] for j in range(1, n+1)))
        for m in range(horizon+1):
            for n in range(horizon+1-m):
                partial = a[n] if m == 0 else sum(i[j] * a[m+n-j] for j in range(1, m+1))
                assert a[m] * a[n] <= partial <= a[m+n]
                checked['abstract_convolution_checks'] += 1
        checked['abstract_convolution_sequences'] += 1

    # Side conditions are necessary, not just type-system conveniences.
    empty_counts = [sum(avoids((), p) for p in perms[n]) for n in range(avoider_max_n+1)]
    assert empty_counts == [0] * (avoider_max_n+1)  # not a SEQ: no empty sequence
    assert not sum_cuts(())                       # exclude zero-size indecomposables explicitly
    assert direct_sum((), (0,)) == direct_sum((0,), ())
    assert avoids((0, 1), (0,)) and not avoids((0, 1), direct_sum((0,), (0,)))
    periodic = [int(n % 2 == 0) for n in range(13)]  # SEQ(Z^2)
    assert periodic[1::2] == [0] * 6 and periodic[2::2] == [1] * 6
    try:
        direct_first(())
    except ValueError:
        pass
    else:
        raise AssertionError('empty first component was accepted')

    return {'max_permutation_size': max_n, 'avoider_max_size': avoider_max_n,
            'forbidden_patterns': len(patterns), 'admissible_orientations': orientations,
            **checked, 'negative_side_condition_tests': 5,
            'all_python_assertions_passed': True, 'lean_compilation_performed': False,
            'note': 'Independent exact finite models; not a Lean parser/elaborator/kernel certificate.'}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-n', type=int, default=8)
    parser.add_argument('--avoider-max-n', type=int, default=7)
    parser.add_argument('--json', type=Path)
    args = parser.parse_args()
    result = run(args.max_n, args.avoider_max_n)
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
