"""Exercise mixed-source reporting and historical audit boundaries without Lean."""

import contextlib
import copy
import hashlib
import io
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))

import yaml

import assumptions
import check_clauses
import check_coverage
import check_exponents
import check_manifest
import paper_anchors
import sync_docs


HISTORICAL_COUNTEREXAMPLE_BLOCK = """theorem Exploding.Frozen.counterexample (d : ℕ) (hd : 2 ≤ d)
    (hFMR : Exploding.External.FeyMeesterRedigLeastAction) :
    ∃ η : Site d → ℤ,
      Explosive η ∧
      (¬ ∀ x : Site d, 2 * (d : ℤ) - 2 ≤ η x) ∧
      (∀ n : ℕ, arrival η ((n : ℤ) • e1 d) ≠ ⊤) ∧
      3 / 2 ≤ limsup (fun n : ℕ => ((arrival η ((n : ℤ) • e1 d)).toNat : ℝ) / (n : ℝ)) atTop ∧
      liminf (fun n : ℕ => ((arrival η ((n : ℤ) • e1 d)).toNat : ℝ) / (n : ℝ)) atTop = 1
"""


HISTORICAL_CROSSING_BLOCK = """theorem Exploding.Frozen.crossing_time (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ k : ℕ, 1 ≤ k ∧ ENNReal.ofReal (1 - δ) ≤ toyLaw d p {η | GoodCube η k}
"""


HISTORICAL_APPROXIMATE_BLOCK = """theorem Exploding.Frozen.approximate_subadditive (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∀ᵐ η ∂(toyLaw d p), ∃ C1 C2 : ℕ, ∀ x : Site d,
      arrival η x ≤ lastArrival η (0 : Site d) x + (C1 : ℕ∞) ∧
        lastArrival η (0 : Site d) x ≤ arrival η x + (C2 : ℕ∞)
"""


class SourceReportingTests(unittest.TestCase):
    def setUp(self):
        original = sync_docs.ROOT
        self.live_manifest = copy.deepcopy(sync_docs.load_manifest())
        self.manifest = copy.deepcopy(self.live_manifest)
        self.manifest["nodes"] = [n for n in self.manifest["nodes"]
                                  if not sync_docs.is_local_definition(n)]
        historical = {
            "thm-counterexample": (
                "exploding.tex:1351-1361 (label theorem:counterexample)",
                HISTORICAL_COUNTEREXAMPLE_BLOCK),
            "prop-crossing-time": (
                "exploding.tex:416-422 (label prop:crossing_time)",
                HISTORICAL_CROSSING_BLOCK),
            "prop-approximate-subadditive": (
                "exploding.tex:886-898 (label prop:approximate_subadditive)",
                HISTORICAL_APPROXIMATE_BLOCK),
        }
        restored = {}
        for nid, (source, block) in historical.items():
            node = next(n for n in self.manifest["nodes"] if n["id"] == nid)
            node.pop("source_pin", None)
            node["source"] = source
            node["version"], node["frozen_sha256"] = sync_docs.HISTORICAL_DECLARATIONS[nid]
            self.assertEqual(hashlib.sha256(block.encode()).hexdigest(), node["frozen_sha256"])
            restored[node["file"]] = block
        live_crossing = next(n for n in self.live_manifest["nodes"]
                             if n["id"] == "prop-crossing-time")
        self.live_crossing_text = (original / live_crossing["file"]).read_text(encoding="utf-8")
        live_approximate = next(n for n in self.live_manifest["nodes"]
                                if n["id"] == "prop-approximate-subadditive")
        self.live_approximate_text = (original / live_approximate["file"]).read_text(encoding="utf-8")
        # This fixture models the historical @4 row exactly: the statement is
        # journal-pinned, so its matching gap belongs to official arXiv instead.
        journal_gaps, official_gaps = self.manifest["coverage_allowed_gaps"][:2]
        journal_gaps["statements"] = [
            gap for gap in journal_gaps["statements"]
            if gap["label"] != "prop:approximate_subadditive"]
        if not any(gap["label"] == "prop:approximate_subadditive"
                   for gap in official_gaps["statements"]):
            official_gaps["statements"].append(
                {"kind": "prop", "line": 740, "label": "prop:approximate_subadditive"})
        directory = tempfile.TemporaryDirectory(prefix="exploding-source-reporting-")
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.revised = "paper/corrected-arxiv/exploding-corrected-arxiv.tex"
        paths = {n["file"] for n in self.manifest["nodes"]}
        paths.update(["paper/exploding.tex", "paper/exploding-arxiv.tex", "paper/defs.tex",
                      self.revised, "paper/corrected-arxiv/defs.tex",
                      "README.md", "CORRESPONDENCE.md", "ASSUMPTIONS.md"])
        for filename in paths:
            target = self.root / filename
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(original / filename, target)
            if filename in restored:
                text = target.read_text(encoding="utf-8")
                start = text.index(check_manifest.BEGIN) + len(check_manifest.BEGIN)
                end = text.index(check_manifest.END)
                target.write_text(text[:start] + "\n" + restored[filename]
                                  + text[end:], encoding="utf-8")
        for module in (sync_docs, assumptions, check_manifest, check_clauses, check_exponents,
                       check_coverage, paper_anchors):
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

    def mixed_manifest(self, include_crossing=False):
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
        if include_crossing:
            crossing = next(n for n in self.manifest["nodes"]
                            if n["id"] == "prop-crossing-time")
            live = next(n for n in self.live_manifest["nodes"]
                        if n["id"] == "prop-crossing-time")
            for key in ("source_pin", "source", "version", "frozen_sha256"):
                crossing[key] = copy.deepcopy(live[key])
            (self.root / crossing["file"]).write_text(self.live_crossing_text, encoding="utf-8")
        self.write_manifest()

    def run_main(self, module):
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            result = module.main()
        return result, out.getvalue()

    def test_legacy_docs_and_audit_scope(self):
        self.assertEqual({n["id"] for n in self.manifest["nodes"] if "source_pin" in n},
                         {"lem-penultimate-cluster", "lem-penultimate-upper-bound",
                          "lem-penultimate-close"})
        result, output = self.run_main(sync_docs)
        self.assertEqual(result, 0, output)
        for module, count in ((check_clauses, 21), (check_exponents, 27)):
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
        self.assertIn("4 `FROZEN` non-External definitions", status)
        self.assertIn("Their literal-body/source audit is required", status)
        self.assertIn("Source coverage is partial", status)
        self.assertIn(sync_docs.HISTORICAL_SHA256, status)
        mapping = sync_docs.paper_map(nodes, pins)
        self.assertIn(f"]({self.revised}#L", mapping)
        self.assertEqual(mapping.count("Non-External definition; literal-body/source audit required"), 4)
        self.assertNotIn("Literal source definition", mapping)
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
        self.assertIn("4 non-External FROZEN definitions", text)
        self.assertIn("Source pin: `paper/exploding.tex`", text)

    def test_only_literal_definitions_do_not_imply_every_result_is_proved(self):
        self.mixed_manifest()
        self.manifest["nodes"] = [n for n in self.manifest["nodes"]
                                  if n["id"].startswith("def-literal-")]
        self.write_manifest()
        text = assumptions.render()
        self.assertIn("No cited inputs are registered", text)
        self.assertIn("4 non-External FROZEN definitions", text)
        self.assertNotIn("every registered", text)

    def test_revised_rows_never_inherit_historical_audit_notes(self):
        self.mixed_manifest()
        for module, count in ((check_clauses, 20), (check_exponents, 26)):
            result, output = self.run_main(module)
            self.assertEqual(result, 0, output)
            self.assertIn(f"{count} historical-source statements", output)
            self.assertIn("thm-counterexample: different source pin:", output)
            self.assertNotIn("thm-counterexample: two displays", output)
            for i in range(4):
                self.assertIn(f"def-literal-{i}: different source pin:", output)

    def test_live_crossing_migration_has_exact_source_partition(self):
        nodes = self.live_manifest["nodes"]
        self.assertEqual(len(nodes), 39)
        groups = {}
        for node in nodes:
            filename = node.get("source_pin", self.live_manifest["source_pin"])["file"]
            groups.setdefault(filename, []).append(node)
        old = groups["paper/exploding.tex"]
        official = groups["paper/exploding-arxiv.tex"]
        revised = groups[self.revised]
        self.assertEqual((len(old), len(official), len(revised)), (29, 4, 6))
        self.assertEqual(sum(n["kind"] == "theorem" for n in old), 22)
        self.assertEqual(sum(n["kind"] == "definition" for n in old), 7)
        self.assertEqual({n["id"] for n in official},
                         {"lem-penultimate-cluster", "lem-penultimate-upper-bound",
                          "lem-penultimate-close", "prop-approximate-subadditive"})
        self.assertTrue(all(n["kind"] == "theorem" for n in official))
        self.assertEqual(sum(n["kind"] == "theorem" for n in revised), 2)
        self.assertEqual(sum(n["kind"] == "definition" for n in revised), 4)
        self.assertEqual({n["id"] for n in revised if n["kind"] == "theorem"},
                         {"thm-counterexample", "prop-crossing-time"})

    def test_live_approximate_successor_coverage_and_historical_boundary(self):
        self.manifest = copy.deepcopy(self.live_manifest)
        self.write_manifest()
        result, output = self.run_main(check_coverage)
        self.assertEqual(result, 0, output)
        self.assertIn("18/24 statements claimed", output)
        self.assertIn("4/24 statements claimed", output)
        self.assertEqual(output.count("2/24 statements claimed"), 1)

        saved = copy.deepcopy(self.manifest["coverage_allowed_gaps"])
        journal, official, _ = self.manifest["coverage_allowed_gaps"]
        journal["statements"] = [
            gap for gap in journal["statements"]
            if gap["label"] != "prop:approximate_subadditive"]
        self.write_manifest()
        result, output = self.run_main(check_coverage)
        self.assertEqual(result, 1, output)
        self.assertIn("unexpected gap: prop at line 886", output)

        self.manifest["coverage_allowed_gaps"] = copy.deepcopy(saved)
        official = self.manifest["coverage_allowed_gaps"][1]
        official["statements"].append(
            {"kind": "prop", "line": 740, "label": "prop:approximate_subadditive"})
        self.write_manifest()
        result, output = self.run_main(check_coverage)
        self.assertEqual(result, 1, output)
        self.assertIn("stale gap allowance: prop at line 740", output)

        node = next(n for n in self.manifest["nodes"]
                    if n["id"] == "prop-approximate-subadditive")
        for defect in ("input", "citation"):
            with self.subTest(defect=defect):
                saved_node = copy.deepcopy(node)
                if defect == "input":
                    node["source_pin"] = {**node["source_pin"], "inputs": []}
                else:
                    node["source"] = "exploding.tex:886-898 (label prop:approximate_subadditive)"
                self.write_manifest()
                for module in (sync_docs, assumptions, check_clauses, check_exponents):
                    result, output = self.run_main(module)
                    self.assertEqual(result, 2, output)
                node.clear()
                node.update(saved_node)

        self.write_manifest()
        for module in (check_clauses, check_exponents):
            result, output = self.run_main(module)
            self.assertEqual(result, 0, output)
            self.assertIn("prop-approximate-subadditive: different source pin:", output)

    def test_historical_approximate_note_cannot_be_reused_for_v5(self):
        node = next(n for n in self.manifest["nodes"]
                    if n["id"] == "prop-approximate-subadditive")
        node["version"] = 5
        self.write_manifest()
        for module in (check_clauses, check_exponents):
            result, output = self.run_main(module)
            self.assertEqual(result, 2, output)
            self.assertIn("historical annotation identity mismatch", output)

    def test_two_migrations_exclude_both_historical_readings(self):
        self.mixed_manifest(include_crossing=True)
        revised = [n for n in self.manifest["nodes"]
                   if n.get("source_pin", {}).get("file") == self.revised]
        self.assertEqual({n["id"] for n in revised if n["kind"] == "theorem"},
                         {"thm-counterexample", "prop-crossing-time"})
        self.assertEqual(sum(n["kind"] == "definition" for n in revised), 4)
        for module, count in ((check_clauses, 19), (check_exponents, 25)):
            result, output = self.run_main(module)
            self.assertEqual(result, 0, output)
            self.assertIn(f"{count} historical-source statements", output)
            for nid in ("thm-counterexample", "prop-crossing-time"):
                self.assertIn(f"{nid}: different source pin:", output)
            self.assertNotIn("prop-crossing-time: one display", output)

    def test_crossing_corrected_pin_and_citation_are_checked(self):
        self.mixed_manifest(include_crossing=True)
        node = next(n for n in self.manifest["nodes"] if n["id"] == "prop-crossing-time")
        for defect in ("input", "citation"):
            with self.subTest(defect=defect):
                saved = copy.deepcopy(node)
                if defect == "input":
                    node["source_pin"] = {**node["source_pin"], "inputs": []}
                else:
                    node["source"] = "exploding.tex:416-422 (label prop:crossing_time)"
                self.write_manifest()
                for module in (sync_docs, assumptions, check_clauses, check_exponents):
                    result, output = self.run_main(module)
                    self.assertEqual(result, 2, output)
                node.clear()
                node.update(saved)

    def test_crossing_successor_cannot_inherit_historical_identity(self):
        self.mixed_manifest(include_crossing=True)
        node = next(n for n in self.manifest["nodes"] if n["id"] == "prop-crossing-time")
        node.pop("source_pin")
        node["source"] = "exploding.tex:416-422 (label prop:crossing_time)"
        self.write_manifest()
        for module in (check_clauses, check_exponents):
            result, output = self.run_main(module)
            self.assertEqual(result, 2, output)
            self.assertIn("historical annotation identity mismatch", output)

    def test_crossing_historical_byte_and_rehash_mutants_fail(self):
        node = next(n for n in self.manifest["nodes"] if n["id"] == "prop-crossing-time")
        path = self.root / node["file"]
        text = path.read_text(encoding="utf-8")
        path.write_text(text.replace(node["export"], node["export"] + " (hExtra : False)", 1),
                        encoding="utf-8")
        for rehash in (False, True):
            if rehash:
                block = check_manifest.block_of(path.read_text(), path, [])[0]
                node["version"] += 1
                node["frozen_sha256"] = hashlib.sha256(block.encode()).hexdigest()
                self.write_manifest()
            for module in (check_clauses, check_exponents):
                result, output = self.run_main(module)
                self.assertEqual(result, 2, output)
                self.assertIn("historical annotation identity mismatch" if rehash
                              else "actual frozen block differs", output)

    def test_crossing_coverage_move_rejects_stale_and_missing_allowances(self):
        self.mixed_manifest(include_crossing=True)
        result, output = self.run_main(check_coverage)
        self.assertEqual(result, 0, output)
        self.assertIn("19/24 statements claimed", output)
        self.assertIn("3/24 statements claimed", output)
        self.assertEqual(output.count("2/24 statements claimed"), 1)
        saved = copy.deepcopy(self.manifest["coverage_allowed_gaps"])
        old, official, revised = self.manifest["coverage_allowed_gaps"]
        old["statements"] = [s for s in old["statements"]
                             if s["label"] != "prop:crossing_time"]
        self.write_manifest()
        result, output = self.run_main(check_coverage)
        self.assertEqual(result, 1, output)
        self.assertIn("unexpected gap", output)
        self.manifest["coverage_allowed_gaps"] = copy.deepcopy(saved)
        self.manifest["coverage_allowed_gaps"][2]["statements"].append(
            {"kind": "prop", "line": 286, "label": "prop:crossing_time"})
        self.write_manifest()
        result, output = self.run_main(check_coverage)
        self.assertEqual(result, 1, output)
        self.assertIn("stale gap allowance", output)

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
        self.assertEqual(result, 2, output)
        self.assertIn("unreviewed-counterexample", output)

    def test_changed_historical_identity_requires_fresh_review(self):
        node = next(n for n in self.manifest["nodes"] if n["id"] == "thm-counterexample")
        node["version"] += 1
        self.write_manifest()
        for module in (check_clauses, check_exponents):
            result, output = self.run_main(module)
            self.assertEqual(result, 2, output)
            self.assertIn("historical annotation identity mismatch", output)

    def test_changed_historical_bytes_cannot_retain_old_hash(self):
        node = next(n for n in self.manifest["nodes"] if n["id"] == "thm-counterexample")
        path = self.root / node["file"]
        text = path.read_text(encoding="utf-8")
        text = text.replace(node["export"], node["export"] + " (hAdditional : False)", 1)
        path.write_text(text, encoding="utf-8")
        for module in (check_clauses, check_exponents):
            result, output = self.run_main(module)
            self.assertEqual(result, 2, output)
            self.assertIn("actual frozen block differs", output)

    def test_updated_version_and_hash_do_not_refresh_historical_notes(self):
        import hashlib

        node = next(n for n in self.manifest["nodes"] if n["id"] == "thm-counterexample")
        path = self.root / node["file"]
        text = path.read_text(encoding="utf-8")
        text = text.replace(node["export"], node["export"] + " (hAdditional : False)", 1)
        path.write_text(text, encoding="utf-8")
        errors = []
        block = check_manifest.block_of(text, path, errors)[0]
        node["version"] += 1
        node["frozen_sha256"] = hashlib.sha256(block.encode()).hexdigest()
        self.write_manifest()
        for module in (check_clauses, check_exponents):
            result, output = self.run_main(module)
            self.assertEqual(result, 2, output)
            self.assertIn("historical annotation identity mismatch", output)


if __name__ == "__main__":
    unittest.main()
