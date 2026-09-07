#!/usr/bin/env python3
"""Fail closed when an executed #print axioms audit is missing or nonstandard."""
from __future__ import annotations

import re
import sys
from pathlib import Path

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
ROOT = Path(__file__).resolve().parents[1]


def audit(text: str, expected: list[str]) -> list[str]:
    errors: list[str] = []
    if not expected:
        return ["no declarations requested for audit"]
    for name in expected:
        pattern = (re.escape(name) + r"'?\s+(?:depends on axioms:\s*\[([^\]]*)\]"
                   r'|does not depend on any axioms)')
        match = re.search(pattern, text)
        if not match:
            errors.append(f'missing audit result: {name}')
            continue
        axioms = {x.strip() for x in (match.group(1) or '').split(',') if x.strip()}
        if axioms - ALLOWED:
            errors.append(f'{name}: unexpected axioms {sorted(axioms - ALLOWED)}')
    return errors


def main() -> int:
    if len(sys.argv) != 2:
        print('usage: check_axioms.py PATH_TO_EXECUTED_AUDIT_LOG', file=sys.stderr)
        return 2
    expected = re.findall(r'^#print axioms\s+(\S+)',
                          (ROOT / 'Audit.lean').read_text(), re.M)
    text = Path(sys.argv[1]).read_text()
    errors = audit(text, expected)
    if errors:
        print('\n'.join(errors), file=sys.stderr)
        return 1
    print(f'PASS executed axiom audit: {len(expected)} declarations; '
          f'allowed axioms: {", ".join(sorted(ALLOWED))}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
