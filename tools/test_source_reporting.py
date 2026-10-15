"""Exercise mixed-source reporting and historical audit boundaries without Lean."""

import contextlib
import copy
import io
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

import yaml

import assumptions
import check_clauses
import check_exponents
import check_manifest
import sync_docs


class SourceReportingTests(unittest.TestCase):
    def setUp(self):
        original = sync_docs.ROOT
        self.manifest = copy.deepcopy(sync_docs.load_manifest())
        self.manifest["nodes"] = [n for n in self.manifest["nodes"]
                                  if not sync_docs.is_literal_definition(n)]
        counterexample = next(n for n in self.manifest["nodes"]
                              if n["id"] == "thm-counterexample")
        counterexample.pop("source_pin", None)
        counterexample["source"] = "exploding.tex:1351-1361 (label theorem:counterexample)"
        directory = tempfile.TemporaryDirectory(prefix="exploding-source-reporting-")
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.revised = "paper/corrected-arxiv/exploding-corrected-arxiv.tex"
        paths = {n["file"] for n in self.manifest["nodes"]}
        paths.update(["paper/exploding.tex", self.revised, "paper/corrected-arxiv/defs.tex",
                      "README.md", "CORRESPONDENCE.md", "ASSUMPTIONS.md"])
        for filename in paths:
            target = self.root / filename
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(original / filename, target)
        for module in (sync_docs, assumptions, check_manifest, check_clauses, check_exponents):
            self.enterContext(patch.object(module, "ROOT", self.root))
            if hasattr(module, "MANIFEST"):
                self.enterContext(patch.object(module, "MANIFEST", self.root / "ledger/manifest.yaml"))
        self.enterContext(patch.dict(os.environ))
        os.environ.pop("EXPLODING_PAPER", None)
        self.enterContext(patch.object(sys, "argv", ["source-reporting-test"]))
        self.write_manifest()
        with patch.object(sys, "argv", ["sync_docs.py", "--write"]):
            result, output = self.run_main(sync_docs)
        self.assertEqual(result, 0, output)

    def write_manifest(self):
        path = self.root / "ledger/manifest.yaml"
        path.parent.mkdir(exist_ok=True)
        path.write_text(yaml.safe_dump(self.manifest), encoding="utf-8")

    def mixed_manifest(self):
        import hashlib

        def pin(filename):
            return {"file": filename,
                    "sha256": hashlib.sha256((self.root / filename).read_bytes()).hexdigest()}

        source_pin = {**pin(self.revised),
                      "inputs": [pin("paper/corrected-arxiv/defs.tex")]}
        env = next(e for e in sync_docs.paper_environments(self.revised)
                   if e["label"] == "theorem:counterexample")
        revised = next(n for n in self.manifest["nodes"] if n["id"] == "thm-counterexample")
        revised["source_pin"] = source_pin
        revised["source"] = (f"exploding-corrected-arxiv.tex:{env['start']}-{env['end']} "
                             "(label theorem:counterexample)")
        for i in range(4):
            export = f"Exploding.Frozen.testLiteral{i}"
            filename = f"Exploding/Frozen/TestLiteral{i}.lean"
            (self.root / filename).write_text(
                "-- FROZEN-STATEMENT-BEGIN\n"
                f"noncomputable def {export} : Nat := {i}\n"
                "-- FROZEN-STATEMENT-END\n", encoding="utf-8")
            self.manifest["nodes"].append({
                "id": f"def-literal-{i}", "kind": "definition", "state": "FROZEN",
                "file": filename, "export": export, "source_pin": source_pin,
                "source": "exploding-corrected-arxiv.tex:1-2 (literal definition)",
            })
        self.write_manifest()

    def run_main(self, module):
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            result = module.main()
        return result, out.getvalue()

    def test_legacy_docs_and_audit_scope(self):
        result, output = self.run_main(sync_docs)
        self.assertEqual(result, 0, output)
        for module, count in ((check_clauses, 24), (check_exponents, 30)):
            result, output = self.run_main(module)
            self.assertEqual(result, 0, output)
            self.assertIn(f"{count} historical-source statements", output)

    def test_mixed_docs_distinguish_sources_and_literal_definitions(self):
        self.mixed_manifest()
        nodes = self.manifest["nodes"]
        pins = sync_docs.source_pins(nodes, self.manifest)
        status = sync_docs.status_block(nodes, pins)
        self.assertIn("39 registered declarations", status)
        self.assertIn("7 `FROZEN` cited inputs", status)
        self.assertIn("4 `FROZEN` literal definitions", status)
        self.assertIn("Source coverage is partial", status)
        self.assertIn(sync_docs.HISTORICAL_SHA256, status)
        mapping = sync_docs.paper_map(nodes, pins)
        self.assertIn(f"]({self.revised}#L", mapping)
        self.assertEqual(mapping.count("Literal source definition"), 4)
        self.assertIn("TestLiteral0.lean#L2", mapping)
        with patch.object(sys, "argv", ["sync_docs.py", "--write"]):
            result, output = self.run_main(sync_docs)
        self.assertEqual(result, 0, output)
        result, output = self.run_main(sync_docs)
        self.assertEqual(result, 0, output)

    def test_literal_definitions_are_not_assumed_inputs(self):
        self.mixed_manifest()
        text = assumptions.render()
        self.assertEqual(text.count("\n## `"), 7)
        self.assertNotIn("## `def-literal-", text)
        self.assertIn("4 FROZEN literal definitions", text)
        self.assertIn("Source pin: `paper/exploding.tex`", text)

    def test_only_literal_definitions_do_not_imply_every_result_is_proved(self):
        self.mixed_manifest()
        self.manifest["nodes"] = [n for n in self.manifest["nodes"]
                                  if n["id"].startswith("def-literal-")]
        self.write_manifest()
        text = assumptions.render()
        self.assertIn("No cited inputs are registered", text)
        self.assertIn("4 FROZEN literal definitions", text)
        self.assertNotIn("every registered", text)

    def test_revised_rows_never_inherit_historical_audit_notes(self):
        self.mixed_manifest()
        for module, count in ((check_clauses, 23), (check_exponents, 29)):
            result, output = self.run_main(module)
            self.assertEqual(result, 0, output)
            self.assertIn(f"{count} historical-source statements", output)
            self.assertIn("thm-counterexample: different source pin:", output)
            self.assertNotIn("thm-counterexample: two displays", output)
            for i in range(4):
                self.assertIn(f"def-literal-{i}: different source pin:", output)

    def test_empty_historical_audit_fails(self):
        self.mixed_manifest()
        self.manifest["nodes"] = [n for n in self.manifest["nodes"] if "source_pin" in n]
        self.write_manifest()
        for module in (check_clauses, check_exponents):
            result, output = self.run_main(module)
            self.assertEqual(result, 1, output)
            self.assertIn("no historical-source statements compared", output)

    def test_stale_pin_and_citation_fail_all_reporting_tools(self):
        self.mixed_manifest()
        node = next(n for n in self.manifest["nodes"] if n["id"] == "thm-counterexample")
        for defect in ("input", "citation"):
            with self.subTest(defect=defect):
                saved = copy.deepcopy(node)
                if defect == "input":
                    node["source_pin"] = {**node["source_pin"], "inputs": []}
                else:
                    node["source"] = "exploding.tex:1351-1361 (label theorem:counterexample)"
                self.write_manifest()
                for module in (sync_docs, assumptions, check_clauses, check_exponents):
                    result, output = self.run_main(module)
                    self.assertEqual(result, 2, output)
                node.clear()
                node.update(saved)

    def test_paper_override_cannot_reuse_historical_readings(self):
        os.environ["EXPLODING_PAPER"] = str(self.root / self.revised)
        for module in (check_clauses, check_exponents):
            result, output = self.run_main(module)
            self.assertEqual(result, 2, output)
            self.assertIn("apply only to historical", output)

    def test_unreviewed_historical_statement_still_fails(self):
        node = next(n for n in self.manifest["nodes"] if n["id"] == "thm-counterexample")
        node["id"] = "unreviewed-counterexample"
        self.write_manifest()
        result, output = self.run_main(check_clauses)
        self.assertEqual(result, 1, output)
        self.assertIn("unreviewed-counterexample", output)


if __name__ == "__main__":
    unittest.main()
