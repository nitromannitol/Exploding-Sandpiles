"""Regression checks for exact-source coverage and explicitly scoped repairs."""

from copy import deepcopy
import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

import yaml


ROOT = Path(__file__).resolve().parent.parent


class IndentedDumper(yaml.SafeDumper):
    """Retain the manifest's two-space list indentation in temporary fixtures."""

    def increase_indent(self, flow=False, indentless=False):
        return super().increase_indent(flow, False)


class SourceToolsTest(unittest.TestCase):
    """Exercise scripts in temporary repositories without invoking Lean."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="source-tools-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for directory in ("tools", "paper", "ledger"):
            (self.root / directory).mkdir()
        for name in ("check_manifest", "check_coverage", "paper_anchors", "paper_citations"):
            shutil.copyfile(ROOT / "tools" / f"{name}.py",
                            self.root / "tools" / f"{name}.py")
        self.text = (ROOT / "paper/exploding.tex").read_text()
        (self.root / "paper/exploding.tex").write_text(self.text)
        (self.root / "paper/revised.tex").write_text(self.text)
        self.pin = {"file": "paper/revised.tex",
                    "sha256": hashlib.sha256(self.text.encode()).hexdigest()}
        self.statements, nodes = [], []
        for number, match in enumerate(re.finditer(
                r"\\begin\{(theorem|lemma|proposition|prop|corollary)\}", self.text)):
            kind = match.group(1)
            line = self.text[:match.start()].count("\n") + 1
            end = self.text[:self.text.index(f"\\end{{{kind}}}", match.end())].count("\n") + 1
            first_line = self.text[match.start():].splitlines()[0]
            label_match = re.search(r"\\label\{([^}]+)\}", first_line)
            label = label_match.group(1) if label_match else None
            self.statements.append({"kind": kind, "line": line, "label": label})
            nid, name = f"statement-{number}", f"Statement{number}"
            if label == "theorem:counterexample":
                nid, name = "thm-counterexample", "Counterexample"
            elif label == "theorem:limit_shape":
                nid, name = "thm-limit-shape", "LimitShape"
            nodes.append({"id": nid, "version": 1, "kind": "theorem", "state": "PROVED",
                          "file": f"Exploding/Frozen/{name}.lean",
                          "source": f"exploding.tex:{line}-{end}" +
                          (f" (label {label})" if label else "")})
        for number in range(4):
            node = deepcopy(nodes[0])
            node.update(id=f"companion-{number}",
                        file=f"Exploding/External/Companion{number}.lean")
            nodes.append(node)
        for number in range(7):
            node = deepcopy(nodes[number])
            node.update(id=f"cited-{number}", kind="definition", state="FROZEN",
                        file=f"Exploding/External/Cited{number}.lean")
            nodes.append(node)
        self.original = {"version": 1,
                         "source_pin": {**self.pin, "file": "paper/exploding.tex"},
                         "nodes": nodes}
        self.manifest = deepcopy(self.original)
        self.target = next(node for node in self.manifest["nodes"]
                           if node["id"] == "thm-counterexample")
        self.target["source_pin"] = deepcopy(self.pin)
        self.target["source"] = self.target["source"].replace("exploding.tex", "revised.tex")
        self.target["version"] += 1
        for number in range(4):
            self.manifest["nodes"].append({
                "id": f"literal-{number}", "kind": "definition", "state": "FROZEN",
                "file": f"Exploding/Frozen/Literal{number}.lean",
                "source_pin": deepcopy(self.pin), "source": self.target["source"]})
        self.counterexample = next(s for s in self.statements
                                   if s["label"] == "theorem:counterexample")

    def write_manifest(self):
        (self.root / "ledger/manifest.yaml").write_text(
            yaml.dump(self.manifest, Dumper=IndentedDumper, sort_keys=False))

    def run_script(self, name, *args, paper=None):
        self.write_manifest()
        env = {key: value for key, value in os.environ.items() if key != "EXPLODING_PAPER"}
        if paper is not None:
            env["EXPLODING_PAPER"] = paper
        return subprocess.run([sys.executable, f"tools/{name}.py", *args], cwd=self.root,
                              env=env, text=True, capture_output=True)

    def allow_partial(self):
        self.manifest["coverage_allowed_gaps"] = [
            {"source_pin": deepcopy(self.original["source_pin"]),
             "reason": "The counterexample now has a revised-source owner.",
             "statements": [deepcopy(self.counterexample)]},
            {"source_pin": deepcopy(self.pin),
             "reason": "Only the counterexample is registered for this source.",
             "statements": [deepcopy(s) for s in self.statements
                            if s != self.counterexample]}]

    def test_original_manifest_remains_complete(self):
        self.manifest = deepcopy(self.original)
        result = self.run_script("check_coverage")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("24/24 statements claimed", result.stdout)
        self.assertIn("independent statement and proof audits are still required", result.stdout)
        self.assertNotIn("is formalized", result.stdout)

    def test_mixed_sources_have_no_cross_source_credit(self):
        self.assertEqual(len(self.manifest["nodes"]), 39)
        result = self.run_script("check_coverage")
        self.assertEqual(result.returncode, 1)
        self.assertIn("23/24 statements claimed", result.stdout)
        self.assertIn("1/24 statements claimed", result.stdout)
        self.assertNotIn("every theorem", result.stdout)

    def test_exact_partial_scope_passes_without_whole_paper_claim(self):
        self.allow_partial()
        result = self.run_script("check_coverage")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.count("PARTIAL scope"), 2)
        self.assertNotIn("every theorem", result.stdout)

    def test_new_gap_is_not_covered_by_partial_permission(self):
        self.allow_partial()
        self.manifest["nodes"] = [n for n in self.manifest["nodes"]
                                  if n["id"] != "thm-limit-shape"]
        result = self.run_script("check_coverage")
        self.assertEqual(result.returncode, 1)
        self.assertIn("unexpected gap", result.stdout)

    def test_stale_gap_permission_fails(self):
        self.allow_partial()
        self.manifest["coverage_allowed_gaps"][1]["statements"].append(self.counterexample)
        result = self.run_script("check_coverage")
        self.assertEqual(result.returncode, 1)
        self.assertIn("stale gap allowance", result.stdout)

    def test_definitions_do_not_claim_their_theorem_label(self):
        self.manifest["nodes"].remove(self.target)
        result = self.run_script("check_coverage")
        self.assertEqual(result.returncode, 1)
        self.assertIn("0/24 statements claimed; 4 definitions excluded", result.stdout)

    def test_bad_source_hash_fails_all_scripts(self):
        self.target["source_pin"]["sha256"] = "0" * 64
        for name in ("check_coverage", "paper_anchors", "paper_citations"):
            with self.subTest(script=name):
                result = self.run_script(name)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("SHA-256", result.stderr)

    def test_source_address_must_match_pin(self):
        self.target["source"] = self.target["source"].replace("revised.tex", "exploding.tex")
        result = self.run_script("check_coverage")
        self.assertEqual(result.returncode, 1)
        self.assertIn("source address does not match", result.stderr)

    def test_gap_metadata_is_strict(self):
        self.allow_partial()
        self.manifest["coverage_allowed_gaps"][0]["statements"][0]["line"] = True
        result = self.run_script("check_coverage")
        self.assertEqual(result.returncode, 1)
        self.assertIn("invalid allowed statement", result.stderr)

    def test_duplicate_allowance_fails(self):
        self.allow_partial()
        self.manifest["coverage_allowed_gaps"].append(
            deepcopy(self.manifest["coverage_allowed_gaps"][0]))
        result = self.run_script("check_coverage")
        self.assertEqual(result.returncode, 1)
        self.assertIn("duplicate coverage allowance", result.stderr)

    def test_unknown_source_allowance_fails(self):
        self.allow_partial()
        (self.root / "paper/unregistered.tex").write_text(self.text)
        self.manifest["coverage_allowed_gaps"][1]["source_pin"]["file"] = "paper/unregistered.tex"
        result = self.run_script("check_coverage")
        self.assertEqual(result.returncode, 1)
        self.assertIn("exact active source pin", result.stderr)

    def test_environment_cannot_select_unregistered_bytes(self):
        for name in ("check_coverage", "paper_anchors", "paper_citations"):
            with self.subTest(script=name):
                result = self.run_script(name, paper=str(self.root / "other.tex"))
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("EXPLODING_PAPER", result.stderr)

    def test_anchor_scope_reports_all_corrected_exclusions(self):
        result = self.run_script("paper_anchors")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("excluded 5 rows from paper/revised.tex", result.stdout)
        self.assertIn("thm-counterexample", result.stdout)
        for number in range(4):
            self.assertIn(f"literal-{number}", result.stdout)

    def test_anchor_fix_preserves_corrected_rows(self):
        old = next(n for n in self.manifest["nodes"] if n["id"] == "thm-limit-shape")
        old["source"] = "exploding.tex:1-2 (label theorem:limit_shape)"
        self.target["source"] = "revised.tex:1-2 (label theorem:counterexample)"
        corrected = deepcopy([n for n in self.manifest["nodes"] if "source_pin" in n])
        result = self.run_script("paper_anchors", "--fix")
        self.assertEqual(result.returncode, 0, result.stderr)
        changed = yaml.safe_load((self.root / "ledger/manifest.yaml").read_text())
        self.assertEqual([n for n in changed["nodes"] if "source_pin" in n], corrected)
        self.assertIn("exploding.tex:246-254", (self.root / "ledger/manifest.yaml").read_text())

    def test_citation_fix_preserves_corrected_headers(self):
        corrected = {}
        for node in self.manifest["nodes"]:
            if "source_pin" in node:
                path = self.root / node["file"]
                path.parent.mkdir(parents=True, exist_ok=True)
                text = ("/-\n`exploding.tex:1-2`, label `theorem:counterexample`\n-/\n"
                        "-- FROZEN-STATEMENT-BEGIN\n")
                path.write_text(text)
                corrected[path] = text
        old = self.root / "Exploding/Frozen/LimitShape.lean"
        old.write_text("/-\n`exploding.tex:1-2`, label `theorem:limit_shape`\n-/\n"
                       "-- FROZEN-STATEMENT-BEGIN\n")
        result = self.run_script("paper_citations", "--fix")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("excluded 5 rows", result.stdout)
        self.assertIn("exploding.tex:246-254", old.read_text())
        for path, before in corrected.items():
            self.assertEqual(path.read_text(), before)

    def test_anchor_fix_is_scoped_even_with_identical_source_strings(self):
        alternate = self.root / "paper/alternate/exploding.tex"
        alternate.parent.mkdir()
        alternate.write_text(self.text)
        for node in self.manifest["nodes"]:
            if "source_pin" in node:
                node["source_pin"]["file"] = "paper/alternate/exploding.tex"
                node["source"] = node["source"].replace("revised.tex", "exploding.tex")
        old = next(n for n in self.manifest["nodes"] if n["id"] == "thm-limit-shape")
        old["source"] = self.target["source"] = "exploding.tex:1-2 (label theorem:limit_shape)"
        self.manifest["nodes"].remove(self.target)
        self.manifest["nodes"].insert(0, self.target)
        result = self.run_script("paper_anchors", "--fix")
        self.assertEqual(result.returncode, 0, result.stderr)
        changed = yaml.safe_load((self.root / "ledger/manifest.yaml").read_text())
        self.assertEqual(changed["nodes"][0], self.target)


if __name__ == "__main__":
    unittest.main()
