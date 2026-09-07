#!/usr/bin/env python3
"""Conservative source hygiene, NOT Lean parsing or kernel verification."""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b")


def code_only(text: str) -> str:
    """Remove nested Lean block comments, line comments, and string literals."""
    out: list[str] = []
    i = 0
    depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                out.extend('  ')
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                out.extend('  ')
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif string:
            if text[i] == '\\':
                out.extend('  ')
                i += 2
            else:
                string = text[i] != '"'
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            out.extend('  ')
            i += 2
        elif text.startswith('--', i):
            j = text.find('\n', i)
            if j < 0:
                out.extend(' ' * (len(text) - i))
                i = len(text)
            else:
                out.extend(' ' * (j - i))
                i = j
        elif text[i] == '"':
            string = True
            out.append(' ')
            i += 1
        else:
            out.append(text[i])
            i += 1
    if depth or string:
        raise ValueError('unterminated comment or string')
    return ''.join(out)


def main() -> int:
    files = sorted(p for p in ROOT.rglob('*.lean') if '.lake' not in p.parts)
    problems: list[str] = []
    declarations = 0
    for path in files:
        relative = path.relative_to(ROOT)
        try:
            text = code_only(path.read_text(encoding='utf-8'))
        except ValueError as error:
            problems.append(f'{relative}: {error}')
            continue
        declarations += len(re.findall(r'\b(?:theorem|lemma|def|abbrev|structure)\s+', text))
        for match in FORBIDDEN.finditer(text):
            line = text.count('\n', 0, match.start()) + 1
            problems.append(f'{relative}:{line}: forbidden token {match.group()}')
        for module in re.findall(r'^import\s+(StanleyWilf(?:\.[\w]+)*)\s*$', text, re.M):
            if not (ROOT / (module.replace('.', '/') + '.lean')).is_file():
                problems.append(f'{relative}: missing local import {module}')
    if problems:
        print('\n'.join(problems), file=sys.stderr)
        return 1
    print(f'PASS source hygiene: {len(files)} Lean files, {declarations} named declarations; '
          'no project proof placeholders/custom axioms; local imports resolve.')
    print('This is NOT a Lean compilation or a transitive kernel-axiom audit.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
