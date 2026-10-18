"""Exercise mixed-source reporting and historical audit boundaries without Lean."""

import contextlib
import copy
import hashlib
import io
import json
import os
from pathlib import Path
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


HISTORICAL_EXPLOSIVE_BLOCK = """theorem Exploding.Frozen.explosive (d : ℕ) (hd : 2 ≤ d) (ν : Measure ℤ) (hν : IsProbabilityMeasure ν)
    (hlow : ν {m : ℤ | (d : ℤ) ≤ m} = 1) (hhit : 0 < ν {(2 * (d : ℤ) - 1)})
    (hSch : Exploding.External.SchonmannBootstrap) :
    ∀ᵐ β ∂(Measure.infinitePi fun _ : Site d => ν), Explosive β
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


HISTORICAL_LASTWAVE_BLOCK = """theorem Exploding.Frozen.convergence_of_the_last_wave (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ N : (Fin d → ℝ) → ℝ,
      Continuous N ∧
      ConvexOn ℝ Set.univ N ∧
      (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
      ∀ᵐ η ∂(toyLaw d p),
        (∀ x : Site d, lastArrival η (0 : Site d) x ≠ ⊤) ∧
          ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
            ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
              |((lastArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
                - N y| ≤ ε
"""


HISTORICAL_TIMECONSTANT_BLOCK = """theorem Exploding.Frozen.convergence_of_time_constant (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hFLP : Exploding.External.FeyLevinePeresExplosive)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ N : (Fin d → ℝ) → ℝ,
      Continuous N ∧
      ConvexOn ℝ Set.univ N ∧
      (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
      ∀ᵐ η ∂(toyLaw d p),
        Explosive η ∧ (∀ x : Site d, arrival η x ≠ ⊤) ∧
          ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
            ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
              |((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ) - N y| ≤ ε
"""


HISTORICAL_RENORMALIZATION_BLOCK = """theorem Exploding.Frozen.renormalization_properties (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᵐ η ∂(toyLaw d p),
        ∃ Cinf : Set (Site d), IsInfiniteConnectedGoodSet η k Cinf ∧
          (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)),
            x ∉ Cinf →
              (componentIn Cinfᶜ x).Finite ∧
                ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2)) ∧
          (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ Cinf, ∀ y ∈ Cinf,
            mnorm x ≤ (n : ℤ) → Real.log n ^ (2 : ℕ) ≤ (mnorm (x - y) : ℝ) →
              ∃ m : ℕ, chemDist Cinf x y = (m : ℕ∞) ∧
                c * (mnorm (x - y) : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ C * (mnorm (x - y) : ℝ))
"""


RENORMALIZATION_V5_BLOCK = """theorem Exploding.Frozen.renormalization_properties (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᵐ η ∂(toyLaw d p),
        ∃ Cinf : Set (Site d), IsInfiniteConnectedGoodSet η k Cinf ∧
          (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)),
            x ∉ Cinf →
              (componentIn Cinfᶜ x).Finite ∧
                ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2)) ∧
          (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ Cinf, ∀ y ∈ Cinf,
            mnorm x ≤ (n : ℤ) → Real.log n ^ (2 : ℕ) ≤ (mnorm (x - y) : ℝ) →
              ∃ m : ℕ, chemDist Cinf x y = (m : ℕ∞) ∧
                c * (mnorm (x - y) : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ C * (mnorm (x - y) : ℝ)) ∧
          (∃ z ∈ goodSites η k, Cinf = componentIn (goodSites η k) z) ∧
          (∀ z ∈ goodSites η k, (componentIn (goodSites η k) z).Infinite →
            componentIn (goodSites η k) z = Cinf)
"""


HISTORICAL_LIMITSHAPE_BLOCK = """theorem Exploding.Frozen.limit_shape (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance)
    (hSch : Exploding.External.SchonmannBootstrap) :
    ∃ B : Set (Fin d → ℝ),
      Convex ℝ B ∧ IsOpen B ∧ B.Nonempty ∧
      ∀ᵐ η ∂(toyLaw d p),
        Tendsto
          (fun t : ℕ =>
            volume (symmDiff
              {y : Fin d → ℝ | 0 < podo (explodingPile η) t (nearestSite ((t : ℝ) • y))} B))
          atTop (nhds 0)
"""


LIMITSHAPE_V5_BLOCK = """theorem Exploding.Frozen.limit_shape (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance)
    (hSch : Exploding.External.SchonmannBootstrap) :
    ∃ B : Set (Fin d → ℝ),
      Convex ℝ B ∧ IsOpen B ∧ B.Nonempty ∧
      ∀ᵐ η ∂(toyLaw d p),
        Tendsto
          (fun t : ℕ =>
            volume (symmDiff
              {y : Fin d → ℝ | 0 < podo (explodingPile η) t (nearestSite ((t : ℝ) • y))} B))
          atTop (nhds 0)
"""


class SourceReportingTests(unittest.TestCase):
    """Historical v10 regressions, independent of the mutable live registry."""

    def setUp(self):
        fixture = Path(__file__).parent / "fixtures/source_reporting/baseline_v10.json"
        snapshot = json.loads(fixture.read_text(encoding="utf-8"))
        self.snapshot_manifest = snapshot["manifest"]
        self.manifest = copy.deepcopy(self.snapshot_manifest)
        self.manifest["nodes"] = [n for n in self.manifest["nodes"]
                                  if not sync_docs.is_local_definition(n)]
        historical = {
            "thm-limit-shape": (
                "exploding.tex:246-254 (label theorem:limit_shape)",
                HISTORICAL_LIMITSHAPE_BLOCK),
            "thm-time-constant": (
                "exploding.tex:259-262 (label theorem:convergence_of_time_constant)",
                HISTORICAL_TIMECONSTANT_BLOCK),
            "thm-counterexample": (
                "exploding.tex:1351-1361 (label theorem:counterexample)",
                HISTORICAL_COUNTEREXAMPLE_BLOCK),
            "prop-crossing-time": (
                "exploding.tex:416-422 (label prop:crossing_time)",
                HISTORICAL_CROSSING_BLOCK),
            "prop-approximate-subadditive": (
                "exploding.tex:886-898 (label prop:approximate_subadditive)",
                HISTORICAL_APPROXIMATE_BLOCK),
            "prop-last-wave-convergence": (
                "exploding.tex:846-852 (label prop:convergence_of_the_last_wave)",
                HISTORICAL_LASTWAVE_BLOCK),
            "prop-renormalization": (
                "exploding.tex:482-497 (label prop:renormalization_properties)",
                HISTORICAL_RENORMALIZATION_BLOCK),
            "thm-explosive": (
                "exploding.tex:265-268 (label theorem:explosive)",
                HISTORICAL_EXPLOSIVE_BLOCK),
        }
        restored = {}
        for nid, (source, block) in historical.items():
            node = next(n for n in self.manifest["nodes"] if n["id"] == nid)
            node.pop("source_pin", None)
            node["source"] = source
            node["version"], node["frozen_sha256"] = sync_docs.HISTORICAL_DECLARATIONS[nid]
            self.assertEqual(hashlib.sha256(block.encode()).hexdigest(), node["frozen_sha256"])
            restored[node["file"]] = block
        self.snapshot_successor_texts = {
            n["id"]: snapshot["files"][n["file"]]
            for n in self.snapshot_manifest["nodes"] if n["id"] in historical}
        self.snapshot_crossing_text = self.snapshot_successor_texts["prop-crossing-time"]
        # Restore historical journal identities and their matching source gap sets.
        journal_gaps, official_gaps, corrected_gaps = self.manifest["coverage_allowed_gaps"]
        journal_gaps["statements"] = [
            gap for gap in journal_gaps["statements"]
            if gap["label"] not in {"prop:approximate_subadditive",
                                    "prop:convergence_of_the_last_wave",
                                    "theorem:convergence_of_time_constant",
                                    "theorem:limit_shape",
                                    "theorem:explosive"}]
        historical_official_gaps = (
            {"kind": "prop", "line": 740, "label": "prop:approximate_subadditive"},
            {"kind": "prop", "line": 706, "label": "prop:convergence_of_the_last_wave"},
        )
        for gap in historical_official_gaps:
            if not any(existing["label"] == gap["label"]
                       for existing in official_gaps["statements"]):
                official_gaps["statements"].append(gap)
        corrected_gaps["statements"].append(
            {"kind": "theorem", "line": 104, "label": "theorem:limit_shape"})
        corrected_gaps["statements"].append(
            {"kind": "theorem", "line": 117,
             "label": "theorem:convergence_of_time_constant"})
        journal_gaps["statements"] = [
            gap for gap in journal_gaps["statements"]
            if gap["label"] != "prop:renormalization_properties"]
        corrected_gaps["statements"].append(
            {"kind": "prop", "line": 352,
             "label": "prop:renormalization_properties"})
        corrected_gaps["statements"].append(
            {"kind": "theorem", "line": 123, "label": "theorem:explosive"})
        directory = tempfile.TemporaryDirectory(prefix="exploding-source-reporting-")
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.revised = "paper/corrected-arxiv/exploding-corrected-arxiv.tex"
        for filename, contents in snapshot["files"].items():
            target = self.root / filename
            target.parent.mkdir(parents=True, exist_ok=True)
            if filename in restored:
                start = contents.index(check_manifest.BEGIN) + len(check_manifest.BEGIN)
                end = contents.index(check_manifest.END)
                contents = contents[:start] + "\n" + restored[filename] + contents[end:]
            target.write_text(contents, encoding="utf-8")
        # Only generated-block delimiters are needed; no production docs are copied.
        (self.root / "README.md").write_text(
            "\n".join((sync_docs.STATUS_BEGIN, sync_docs.STATUS_END,
                       sync_docs.MAP_BEGIN, sync_docs.MAP_END)), encoding="utf-8")
        (self.root / "CORRESPONDENCE.md").write_text(
            sync_docs.SURFACE_BEGIN + "\n" + sync_docs.SURFACE_END, encoding="utf-8")
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

    def restore_snapshot_successors(self):
        """Restore v10 successor identities with their matching frozen marker bytes."""
        self.manifest = copy.deepcopy(self.snapshot_manifest)
        for node in self.manifest["nodes"]:
            if node["id"] not in self.snapshot_successor_texts:
                continue
            text = self.snapshot_successor_texts[node["id"]]
            path = self.root / node["file"]
            path.write_text(text, encoding="utf-8")
            errors = []
            block = check_manifest.block_of(text, path, errors)
            self.assertIsNotNone(block, errors)
            self.assertEqual(hashlib.sha256(block[0].encode("utf-8")).hexdigest(),
                             node["frozen_sha256"])
        self.write_manifest()

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
            successor = next(n for n in self.snapshot_manifest["nodes"]
                        if n["id"] == "prop-crossing-time")
            for key in ("source_pin", "source", "version", "frozen_sha256"):
                crossing[key] = copy.deepcopy(successor[key])
            (self.root / crossing["file"]).write_text(self.snapshot_crossing_text, encoding="utf-8")
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

    def test_v10_source_moves_have_exact_source_partition(self):
        nodes = self.snapshot_manifest["nodes"]
        self.assertEqual(len(nodes), 39)
        groups = {}
        for node in nodes:
            filename = node.get("source_pin", self.snapshot_manifest["source_pin"])["file"]
            groups.setdefault(filename, []).append(node)
        old = groups["paper/exploding.tex"]
        official = groups["paper/exploding-arxiv.tex"]
        revised = groups[self.revised]
        self.assertEqual((len(old), len(official), len(revised)), (24, 5, 10))
        self.assertEqual(sum(n["kind"] == "theorem" for n in old), 17)
        self.assertEqual(sum(n["kind"] == "definition" for n in old), 7)
        self.assertEqual({n["id"] for n in official},
                         {"lem-penultimate-cluster", "lem-penultimate-upper-bound",
                          "lem-penultimate-close", "prop-approximate-subadditive",
                          "prop-last-wave-convergence"})
        self.assertTrue(all(n["kind"] == "theorem" for n in official))
        self.assertEqual(sum(n["kind"] == "theorem" for n in revised), 6)
        self.assertEqual(sum(n["kind"] == "definition" for n in revised), 4)
        self.assertEqual({n["id"] for n in revised if n["kind"] == "theorem"},
                         {"thm-counterexample", "prop-crossing-time", "thm-time-constant",
                          "prop-renormalization", "thm-limit-shape", "thm-explosive"})

    def test_theorem_1_4_v4_excludes_its_v3_historical_reading(self):
        self.restore_snapshot_successors()
        result, output = self.run_main(check_clauses)
        self.assertEqual(result, 0, output)
        self.assertIn("thm-explosive: different source pin:", output)
        node = next(n for n in self.manifest["nodes"] if n["id"] == "thm-explosive")
        self.assertEqual((node["version"], node["source"]),
                         (4, "exploding-corrected-arxiv.tex:123-129 (label theorem:explosive)"))
        node.pop("source_pin")
        node["source"] = "exploding.tex:265-268 (label theorem:explosive)"
        self.write_manifest()
        result, output = self.run_main(check_clauses)
        self.assertEqual(result, 2, output)
        self.assertIn("thm-explosive: historical annotation identity mismatch", output)

    def test_v10_approximate_successor_coverage_and_historical_boundary(self):
        self.restore_snapshot_successors()
        result, output = self.run_main(check_coverage)
        self.assertEqual(result, 0, output)
        self.assertIn("13/24 statements claimed", output)
        self.assertIn("6/24 statements claimed", output)
        self.assertEqual(output.count("5/24 statements claimed"), 1)

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

    def test_v10_timeconstant_source_move_and_negative_controls(self):
        self.restore_snapshot_successors()
        node = next(n for n in self.manifest["nodes"] if n["id"] == "thm-time-constant")
        self.assertEqual((node["version"], node["frozen_sha256"]),
                         (6, "83239bc6236e7faecd7ba0ab147fc0af98c324fc90f32cb537a6f368fa478a07"))
        text = (self.root / node["file"]).read_text(encoding="utf-8")
        block = check_manifest.block_of(text, self.root / node["file"], [])[0]
        self.assertEqual(block, HISTORICAL_TIMECONSTANT_BLOCK.replace(
            "(hp1 : p < 1)", "(hp1 : p ≤ 1)"))
        result, output = self.run_main(check_coverage)
        self.assertEqual(result, 0, output)
        self.assertIn("13/24 statements claimed", output)
        self.assertIn("6/24 statements claimed", output)
        self.assertEqual(output.count("5/24 statements claimed"), 1)
        saved_gaps = copy.deepcopy(self.manifest["coverage_allowed_gaps"])
        for defect in ("missing-journal", "stale-corrected", "unclaimed-official"):
            with self.subTest(defect=defect):
                self.manifest["coverage_allowed_gaps"] = copy.deepcopy(saved_gaps)
                journal, official, corrected = self.manifest["coverage_allowed_gaps"]
                if defect == "stale-corrected":
                    corrected["statements"].append(
                        {"kind": "theorem", "line": 117,
                         "label": "theorem:convergence_of_time_constant"})
                else:
                    group = journal if defect == "missing-journal" else official
                    group["statements"] = [g for g in group["statements"]
                                            if g["label"] != "theorem:convergence_of_time_constant"]
                self.write_manifest()
                result, output = self.run_main(check_coverage)
                self.assertEqual(result, 1, output)
                self.assertIn("stale gap allowance" if defect == "stale-corrected"
                              else "unexpected gap", output)
        self.manifest["coverage_allowed_gaps"] = saved_gaps
        for defect in ("input", "citation"):
            with self.subTest(defect=defect):
                saved = copy.deepcopy(node)
                if defect == "input":
                    node["source_pin"] = {**node["source_pin"], "inputs": []}
                else:
                    node["source"] = "exploding.tex:259-262 (label theorem:convergence_of_time_constant)"
                self.write_manifest()
                for module in (sync_docs, assumptions, check_clauses, check_exponents):
                    result, output = self.run_main(module)
                    self.assertEqual(result, 2, output)
                node.clear()
                node.update(saved)

    def test_v10_renormalization_v5_marker_source_and_gap_controls(self):
        self.restore_snapshot_successors()
        node = next(n for n in self.manifest["nodes"]
                    if n["id"] == "prop-renormalization")
        expected_source = (
            "exploding-corrected-arxiv.tex:352-367 "
            "(label prop:renormalization_properties)")
        expected_pin = {
            "file": self.revised,
            "sha256": "59b5ac1a5cdf80c5b550dfc1738414892e0aa3f8cdb0bf03d00c74685a3e1be2",
            "inputs": [{
                "file": "paper/corrected-arxiv/defs.tex",
                "sha256": "9aba2c73246d79e3c6b87cb1f01cf3e2f636e27c8afd97ccb8ba5c032a9ee65b",
            }],
        }
        self.assertEqual(node["version"], 5)
        self.assertEqual(node["frozen_sha256"],
                         "5e3c8b09f9ce732c2cad76168fa1d455e515ea8a08ae74716d43967e8e623b21")
        self.assertEqual(node["source"], expected_source)
        self.assertEqual(node["source_pin"], expected_pin)
        path = self.root / node["file"]
        text = path.read_text(encoding="utf-8")
        block = check_manifest.block_of(text, path, [])[0]
        self.assertEqual(len(block.encode("utf-8")), 1298)
        self.assertEqual(hashlib.sha256(block.encode("utf-8")).hexdigest(),
                         node["frozen_sha256"])
        self.assertEqual(block, RENORMALIZATION_V5_BLOCK)
        self.assertIn("(∃ z ∈ goodSites η k, Cinf = componentIn (goodSites η k) z)", block)
        self.assertIn("componentIn (goodSites η k) z = Cinf", block)

        for omitted_clause in (
                " ∧\n          (∀ z ∈ goodSites η k, (componentIn (goodSites η k) z).Infinite →\n"
                "            componentIn (goodSites η k) z = Cinf)\n",
                "          (∃ z ∈ goodSites η k, Cinf = componentIn (goodSites η k) z) ∧\n"):
            mutated = block.replace(omitted_clause, "", 1)
            self.assertNotEqual(mutated, block)
            path.write_text(text.replace(block, mutated, 1), encoding="utf-8")
            mutated_block = check_manifest.block_of(
                path.read_text(encoding="utf-8"), path, [])[0]
            node["frozen_sha256"] = hashlib.sha256(
                mutated_block.encode("utf-8")).hexdigest()
            self.write_manifest()
            self.assertEqual(node["frozen_sha256"],
                             hashlib.sha256(mutated_block.encode("utf-8")).hexdigest())
            self.assertNotEqual(node["frozen_sha256"],
                                "5e3c8b09f9ce732c2cad76168fa1d455e515ea8a08ae74716d43967e8e623b21")
            with self.assertRaises(AssertionError):
                self.assertEqual(mutated_block, RENORMALIZATION_V5_BLOCK)
            path.write_text(text, encoding="utf-8")
            node["frozen_sha256"] = hashlib.sha256(block.encode("utf-8")).hexdigest()
            self.write_manifest()
        path.write_text(text, encoding="utf-8")

        result, output = self.run_main(check_coverage)
        self.assertEqual(result, 0, output)
        self.assertIn("13/24 statements claimed", output)
        self.assertIn("6/24 statements claimed", output)
        self.assertEqual(output.count("5/24 statements claimed"), 1)

        saved = copy.deepcopy(node)
        node["source_pin"] = {**node["source_pin"], "inputs": []}
        self.write_manifest()
        for module in (sync_docs, assumptions, check_clauses, check_exponents):
            result, output = self.run_main(module)
            self.assertEqual(result, 2, output)
        node.clear()
        node.update(saved)

        node["source"] = "exploding.tex:482-497 (label prop:renormalization_properties)"
        self.write_manifest()
        for module in (sync_docs, assumptions, check_clauses, check_exponents):
            result, output = self.run_main(module)
            self.assertEqual(result, 2, output)
        node.clear()
        node.update(saved)

        saved_gaps = copy.deepcopy(self.manifest["coverage_allowed_gaps"])
        journal, official, _corrected = self.manifest["coverage_allowed_gaps"]
        journal["statements"] = [
            gap for gap in journal["statements"]
            if gap["label"] != "prop:renormalization_properties"]
        self.write_manifest()
        result, output = self.run_main(check_coverage)
        self.assertEqual(result, 1, output)
        self.assertIn("unexpected gap: prop at line 482", output)

        self.manifest["coverage_allowed_gaps"] = copy.deepcopy(saved_gaps)
        self.manifest["coverage_allowed_gaps"][2]["statements"].append(
            {"kind": "prop", "line": 352,
             "label": "prop:renormalization_properties"})
        self.write_manifest()
        result, output = self.run_main(check_coverage)
        self.assertEqual(result, 1, output)
        self.assertIn("stale gap allowance: prop at line 352", output)

        self.manifest["coverage_allowed_gaps"] = copy.deepcopy(saved_gaps)
        node["source_pin"] = {
            "file": "paper/exploding-arxiv.tex",
            "sha256": "f12deba6e481a3d81c6967bc48ecbbdae1df4fa1c5f6248a38990030b308072d",
            "inputs": [{"file": "paper/defs.tex",
                        "sha256": "9aba2c73246d79e3c6b87cb1f01cf3e2f636e27c8afd97ccb8ba5c032a9ee65b"}],
        }
        node["source"] = "exploding-arxiv.tex:344-359 (label prop:renormalization_properties)"
        self.write_manifest()
        result, output = self.run_main(check_coverage)
        self.assertEqual(result, 1, output)
        self.assertIn("stale gap allowance: prop at line 344", output)

    def test_v10_limitshape_v5_partition_source_and_gap_controls(self):
        self.manifest = copy.deepcopy(self.snapshot_manifest)
        self.write_manifest()
        node = next(n for n in self.manifest["nodes"] if n["id"] == "thm-limit-shape")
        self.assertEqual(node["version"], 5)
        self.assertEqual(node["source"],
                         "exploding-corrected-arxiv.tex:104-112 (label theorem:limit_shape)")
        self.assertEqual(node["source_pin"], {
            "file": self.revised,
            "sha256": "59b5ac1a5cdf80c5b550dfc1738414892e0aa3f8cdb0bf03d00c74685a3e1be2",
            "inputs": [{
                "file": "paper/corrected-arxiv/defs.tex",
                "sha256": "9aba2c73246d79e3c6b87cb1f01cf3e2f636e27c8afd97ccb8ba5c032a9ee65b",
            }],
        })
        result, output = self.run_main(check_coverage)
        self.assertEqual(result, 0, output)
        self.assertIn("13/24 statements claimed", output)
        self.assertIn("6/24 statements claimed", output)
        self.assertEqual(output.count("5/24 statements claimed"), 1)

        saved_gaps = copy.deepcopy(self.manifest["coverage_allowed_gaps"])
        for defect in ("journal-246", "corrected-104", "official-101"):
            with self.subTest(defect=defect):
                self.manifest["coverage_allowed_gaps"] = copy.deepcopy(saved_gaps)
                journal, official, corrected = self.manifest["coverage_allowed_gaps"]
                if defect == "journal-246":
                    journal["statements"] = [
                        gap for gap in journal["statements"]
                        if gap["label"] != "theorem:limit_shape"]
                    expected = "unexpected gap: theorem at line 246"
                elif defect == "corrected-104":
                    corrected["statements"].append(
                        {"kind": "theorem", "line": 104, "label": "theorem:limit_shape"})
                    expected = "stale gap allowance: theorem at line 104"
                else:
                    official["statements"] = [
                        gap for gap in official["statements"]
                        if gap["label"] != "theorem:limit_shape"]
                    expected = "unexpected gap: theorem at line 101"
                self.write_manifest()
                result, output = self.run_main(check_coverage)
                self.assertEqual(result, 1, output)
                self.assertIn(expected, output)
        self.manifest["coverage_allowed_gaps"] = copy.deepcopy(saved_gaps)
        self.write_manifest()

        for defect in ("input", "citation"):
            with self.subTest(defect=defect):
                saved = copy.deepcopy(node)
                if defect == "input":
                    node["source_pin"] = {**node["source_pin"], "inputs": []}
                else:
                    node["source"] = "exploding.tex:246-254 (label theorem:limit_shape)"
                self.write_manifest()
                for module in (sync_docs, assumptions, check_clauses, check_exponents):
                    result, output = self.run_main(module)
                    self.assertEqual(result, 2, output)
                    self.assertIn("thm-limit-shape", output)
                node.clear()
                node.update(saved)

    def test_v10_limitshape_v5_frozen_bytes_are_installed(self):
        node = next(n for n in self.snapshot_manifest["nodes"] if n["id"] == "thm-limit-shape")
        text = self.snapshot_successor_texts["thm-limit-shape"]
        block = check_manifest.block_of(text, self.root / node["file"], [])[0]
        self.assertEqual(block, LIMITSHAPE_V5_BLOCK)
        self.assertEqual(hashlib.sha256(block.encode("utf-8")).hexdigest(),
                         node["frozen_sha256"])

    def test_limitshape_v5_marker_bytes_and_single_delta_are_exact(self):
        node = next(n for n in self.snapshot_manifest["nodes"] if n["id"] == "thm-limit-shape")
        self.assertEqual(node["version"], 5)
        self.assertEqual(len(LIMITSHAPE_V5_BLOCK.encode("utf-8")), 652)
        self.assertEqual(hashlib.sha256(LIMITSHAPE_V5_BLOCK.encode("utf-8")).hexdigest(),
                         node["frozen_sha256"])
        self.assertEqual(LIMITSHAPE_V5_BLOCK,
                         HISTORICAL_LIMITSHAPE_BLOCK.replace("(hp1 : p < 1)", "(hp1 : p ≤ 1)", 1))
        # Wrong markers must fail the manifest byte binding: the retained strict
        # endpoint, a dropped cited input, and a dropped conclusion conjunct.
        wrong_markers = (
            HISTORICAL_LIMITSHAPE_BLOCK,
            LIMITSHAPE_V5_BLOCK.replace(
                "(hChem : Exploding.External.AntalPisztoraChemicalDistance)\n"
                "    (hSch : Exploding.External.SchonmannBootstrap) :",
                "(hChem : Exploding.External.AntalPisztoraChemicalDistance) :", 1),
            LIMITSHAPE_V5_BLOCK.replace("IsOpen B ∧ B.Nonempty ∧", "IsOpen B ∧", 1),
        )
        for index, marker in enumerate(wrong_markers):
            with self.subTest(wrong_marker=index):
                self.assertNotEqual(marker, LIMITSHAPE_V5_BLOCK)
                self.assertNotEqual(hashlib.sha256(marker.encode("utf-8")).hexdigest(),
                                    node["frozen_sha256"])

    def test_limitshape_v4_historical_identity_and_bytes_are_exact(self):
        node = next(n for n in self.manifest["nodes"] if n["id"] == "thm-limit-shape")
        self.assertEqual(sync_docs.HISTORICAL_DECLARATIONS["thm-limit-shape"],
                         (4, "7a9bc664298b2adfc0b528e3f1d6ba565efdcb2da1d055eb6e222032e835b44b"))
        self.assertEqual(node["version"], 4)
        self.assertEqual(node["source"], "exploding.tex:246-254 (label theorem:limit_shape)")
        self.assertNotIn("source_pin", node)
        path = self.root / node["file"]
        text = path.read_text(encoding="utf-8")
        block = check_manifest.block_of(text, path, [])[0]
        self.assertEqual(block, HISTORICAL_LIMITSHAPE_BLOCK)

        saved = copy.deepcopy(node)
        node["version"] = 5
        self.write_manifest()
        for module in (check_clauses, check_exponents):
            result, output = self.run_main(module)
            self.assertEqual(result, 2, output)
            self.assertIn("historical annotation identity mismatch", output)
        node.clear()
        node.update(saved)

        path.write_text(text.replace("(hp1 : p < 1)", "(hp1 : p ≤ 1)", 1), encoding="utf-8")
        self.write_manifest()
        for module in (check_clauses, check_exponents):
            result, output = self.run_main(module)
            self.assertEqual(result, 2, output)
            self.assertIn("actual frozen block differs", output)
        path.write_text(text, encoding="utf-8")
        node.clear()
        node.update(saved)
        self.write_manifest()

    def test_renormalization_v4_historical_identity_and_bytes_are_exact(self):
        node = next(n for n in self.manifest["nodes"]
                    if n["id"] == "prop-renormalization")
        self.assertEqual(sync_docs.HISTORICAL_DECLARATIONS["prop-renormalization"],
                         (4, "79b4e8c59d8d852b23963f9f48ecd2a4c39a6d1e66163c3eaa41f57c08ade127"))
        self.assertEqual(node["version"], 4)
        self.assertEqual(node["source"],
                         "exploding.tex:482-497 (label prop:renormalization_properties)")
        self.assertNotIn("source_pin", node)
        path = self.root / node["file"]
        text = path.read_text(encoding="utf-8")
        block = check_manifest.block_of(text, path, [])[0]
        self.assertEqual(block, HISTORICAL_RENORMALIZATION_BLOCK)

        saved = copy.deepcopy(node)
        node["version"] = 5
        self.write_manifest()
        for module in (check_clauses, check_exponents):
            result, output = self.run_main(module)
            self.assertEqual(result, 2, output)
            self.assertIn("historical annotation identity mismatch", output)
        node.clear()
        node.update(saved)

        path.write_text(text.replace(
            "(hp1 : p < 1)", "(hp1 : p ≤ 1)", 1), encoding="utf-8")
        self.write_manifest()
        for module in (check_clauses, check_exponents):
            result, output = self.run_main(module)
            self.assertEqual(result, 2, output)
            self.assertIn("actual frozen block differs", output)

        changed = path.read_text(encoding="utf-8")
        block = check_manifest.block_of(changed, path, [])[0]
        node["frozen_sha256"] = hashlib.sha256(block.encode("utf-8")).hexdigest()
        self.write_manifest()
        for module in (check_clauses, check_exponents):
            result, output = self.run_main(module)
            self.assertEqual(result, 2, output)
            self.assertIn("historical annotation identity mismatch", output)

    def test_timeconstant_historical_identity_and_extra_binder_fail(self):
        node = next(n for n in self.manifest["nodes"] if n["id"] == "thm-time-constant")
        path = self.root / node["file"]
        text = path.read_text(encoding="utf-8")
        for defect in ("version", "extra-binder", "rehashed-extra-binder"):
            with self.subTest(defect=defect):
                saved = copy.deepcopy(node)
                path.write_text(text, encoding="utf-8")
                if defect == "version":
                    node["version"] = 6
                else:
                    changed = text.replace(node["export"],
                                           node["export"] + " (hEndpoint : False)", 1)
                    path.write_text(changed, encoding="utf-8")
                    if defect == "rehashed-extra-binder":
                        node["version"] = 6
                        block = check_manifest.block_of(changed, path, [])[0]
                        node["frozen_sha256"] = hashlib.sha256(block.encode()).hexdigest()
                self.write_manifest()
                for module in (check_clauses, check_exponents):
                    result, output = self.run_main(module)
                    self.assertEqual(result, 2, output)
                    self.assertIn("actual frozen block differs" if defect == "extra-binder"
                                  else "historical annotation identity mismatch", output)
                node.clear()
                node.update(saved)

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


class LiveSourceReportingTests(unittest.TestCase):
    """Check the actual corrected v11 registry separately from historical data."""

    CORRECTED_SHA256 = "c99ce52a57b7da1f805efe610c474c968c0aa00e0840bd8b0e92ae0d4c53f262"

    def setUp(self):
        original = sync_docs.ROOT
        self.manifest = copy.deepcopy(sync_docs.load_manifest())
        directory = tempfile.TemporaryDirectory(prefix="exploding-live-reporting-")
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        pins = sync_docs.source_pins(self.manifest["nodes"], self.manifest)
        # Read current source and declaration bytes, never the v10 fixture.
        paths = {n["file"] for n in self.manifest["nodes"]}
        # A valid but inactive official source is needed for the scope mutant.
        paths.update({"paper/exploding-arxiv.tex", "paper/defs.tex"})
        for pin in pins.values():
            paths.add(pin["file"])
            paths.update(p["file"] for p in pin.get("inputs", []))
        for filename in paths:
            target = self.root / filename
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((original / filename).read_bytes())
        for module in (sync_docs, check_manifest, check_coverage, paper_anchors):
            self.enterContext(patch.object(module, "ROOT", self.root))
            self.enterContext(patch.object(module, "MANIFEST", self.root / "ledger/manifest.yaml"))
        self.enterContext(patch.dict(os.environ))
        os.environ.pop("EXPLODING_PAPER", None)
        self.write_manifest()

    write_manifest = SourceReportingTests.write_manifest
    run_main = SourceReportingTests.run_main

    def test_live_v11_identities_and_source_partition(self):
        nodes = self.manifest["nodes"]
        self.assertEqual(len(nodes), 42)
        self.assertEqual(self.manifest["source_pin"]["sha256"], self.CORRECTED_SHA256)
        _, groups = paper_anchors.manifest_sources(self.manifest)
        self.assertEqual({key[0]: len(group["nodes"]) for key, group in groups.items()},
                         {"paper/exploding.tex": 13,
                          "paper/corrected-arxiv/exploding-corrected-arxiv.tex": 29})
        corrected = groups[(self.manifest["source_pin"]["file"], self.CORRECTED_SHA256)]
        # 22 numbered paper-owned statements and the unnumbered planar optimality remark.
        self.assertEqual(sum(n["kind"] == "theorem" for n in corrected["nodes"]), 23)
        self.assertEqual(sum(sync_docs.is_local_definition(n) for n in nodes), 4)
        self.assertEqual(sum(sync_docs.is_cited_external(n) for n in nodes), 9)
        for node in nodes:
            with self.subTest(node=node["id"]):
                path = self.root / node["file"]
                errors = []
                block = check_manifest.block_of(path.read_text(encoding="utf-8"), path, errors)
                self.assertIsNotNone(block, errors)
                self.assertEqual(hashlib.sha256(block[0].encode("utf-8")).hexdigest(),
                                 node["frozen_sha256"])
                if node["id"] in {
                        "ext-fey-den-boer-redig-cubical-cluster", "ext-fey-levine-peres-radius"}:
                    self.assertEqual(node["version"], 2)
                    self.assertTrue(block[0].startswith(f"def {node['export']} : Prop :=\n"))

    def test_live_default_serialization_preserves_effective_sources_and_partial_scope(self):
        before = sync_docs.source_pins(self.manifest["nodes"], self.manifest)
        self.assertEqual(len(self.manifest["coverage_allowed_gaps"]), 2)
        for node in self.manifest["nodes"]:
            if node.get("source_pin") == self.manifest["source_pin"]:
                node.pop("source_pin")
            else:
                self.assertEqual(node["source_pin"]["file"], "paper/exploding.tex")
        self.assertEqual(sum("source_pin" not in n for n in self.manifest["nodes"]), 29)
        self.write_manifest()
        reloaded = sync_docs.load_manifest()
        self.assertEqual(sync_docs.source_pins(reloaded["nodes"], reloaded), before)
        result, output = self.run_main(check_coverage)
        self.assertEqual(result, 0, output)
        self.assertIn("2/24 statements claimed", output)
        self.assertIn("22/24 statements claimed", output)
        self.assertEqual(output.count("statements claimed;"), 2)
        self.assertIn("whole-paper formalization is not certified", output)

    def test_live_missing_forged_and_inactive_source_scopes_fail(self):
        saved = copy.deepcopy(self.manifest["coverage_allowed_gaps"])
        for defect in ("missing", "forged", "inactive-official"):
            with self.subTest(defect=defect):
                self.manifest["coverage_allowed_gaps"] = copy.deepcopy(saved)
                entries = self.manifest["coverage_allowed_gaps"]
                if defect == "missing":
                    entries.clear()
                    expected = "unexpected gap"
                elif defect == "forged":
                    entries[0]["statements"].append(
                        {"kind": "theorem", "line": 1, "label": "forged:scope"})
                    expected = "stale gap allowance"
                else:
                    entries[0]["source_pin"] = {
                        "file": "paper/exploding-arxiv.tex",
                        "sha256": hashlib.sha256(
                            (self.root / "paper/exploding-arxiv.tex").read_bytes()).hexdigest(),
                        "inputs": [{
                            "file": "paper/defs.tex",
                            "sha256": hashlib.sha256(
                                (self.root / "paper/defs.tex").read_bytes()).hexdigest(),
                        }],
                    }
                    expected = "coverage allowance must select an exact active source pin"
                self.write_manifest()
                result, output = self.run_main(check_coverage)
                self.assertEqual(result, 1, output)
                self.assertIn(expected, output)

    def test_live_corrected_pin_and_citation_reject_stale_data(self):
        node = next(n for n in self.manifest["nodes"] if n["id"] == "lem-square-lower-bound")
        saved = copy.deepcopy(node)
        for defect in ("v10-pin", "missing-input", "journal-citation"):
            with self.subTest(defect=defect):
                node.clear()
                node.update(copy.deepcopy(saved))
                node["source_pin"] = copy.deepcopy(self.manifest["source_pin"])
                if defect == "v10-pin":
                    node["source_pin"]["sha256"] = (
                        "59b5ac1a5cdf80c5b550dfc1738414892e0aa3f8cdb0bf03d00c74685a3e1be2")
                elif defect == "missing-input":
                    node["source_pin"]["inputs"] = []
                else:
                    node["source"] = "exploding.tex:586-603 (label lemma:square_lower_bound)"
                with self.assertRaises(LookupError):
                    sync_docs.source_pins(self.manifest["nodes"], self.manifest)


if __name__ == "__main__":
    unittest.main()
