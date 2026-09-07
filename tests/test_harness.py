"""Regression tests for the verification gates, not for the Lean kernel."""
from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def load(name: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / f'{name}.py')
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


sources = load('check_sources')
axioms = load('check_axioms')


class SourceTests(unittest.TestCase):
    def test_nested_comments(self):
        text = '/- axiom /- sorry -/ admit -/\ntheorem x : True := by trivial'
        self.assertIsNone(sources.FORBIDDEN.search(sources.code_only(text)))

    def test_strings_and_comments_not_code(self):
        text = 'def s := "axiom \\\"sorry" -- admit\n'
        self.assertIsNone(sources.FORBIDDEN.search(sources.code_only(text)))

    def test_real_placeholder_rejected(self):
        text = '/- explanatory comment -/\ntheorem x : False := by sorry'
        self.assertEqual(sources.FORBIDDEN.search(sources.code_only(text)).group(), 'sorry')

    def test_custom_axiom_rejected(self):
        self.assertIsNotNone(sources.FORBIDDEN.search(sources.code_only('axiom x : False')))

    def test_unterminated_comment_rejected(self):
        with self.assertRaises(ValueError):
            sources.code_only('/- unfinished')


class AxiomTests(unittest.TestCase):
    def test_standard_axioms_accepted(self):
        self.assertEqual(axioms.audit("'X' depends on axioms: [propext, Classical.choice, Quot.sound]", ['X']), [])

    def test_no_axioms_accepted(self):
        self.assertEqual(axioms.audit("'X' does not depend on any axioms", ['X']), [])

    def test_missing_result_rejected(self):
        self.assertTrue(axioms.audit('', ['X']))

    def test_empty_requested_audit_rejected(self):
        self.assertTrue(axioms.audit('', []))

    def test_sorry_axiom_rejected(self):
        self.assertTrue(axioms.audit("'X' depends on axioms: [sorryAx]", ['X']))

    def test_custom_axiom_rejected(self):
        self.assertTrue(axioms.audit("'X' depends on axioms: [SomeUnprovedTheorem]", ['X']))


if __name__ == '__main__':
    unittest.main()
