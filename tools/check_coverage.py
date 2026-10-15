"""Check that every theorem-like statement in the paper is formalized.

The manifest says which paper statement each Lean node transcribes.  This asks
the complementary question, which no other checker asks: is there a statement in
the paper that no node claims?  A formalization can be entirely axiom-clean and
still be silently incomplete, so the gap is worth a gate of its own.

Open problems (the `problem` environment of Section 9) are excluded: they are
questions, not claims.

Each effective exact source pin is checked separately. Definitions never claim
theorem coverage. Partial coverage requires an exact, explicit manifest entry:

    coverage_allowed_gaps:
      - source_pin: {file: paper/example.tex, sha256: <exact digest>}
        reason: <explanation of the intentionally partial scope>
        statements:
          - {kind: theorem, line: 10, label: "theorem:example"}

Use ``label: null`` for an unlabelled statement. The listed set must equal the
actual uncovered set; stale allowances and unexpected gaps both fail. A passing
partial check records the approved scope, never whole-paper formalization.

    python3 tools/check_coverage.py
"""

from __future__ import annotations

import os
import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    sys.exit("check_coverage.py: PyYAML is required (pip install pyyaml)")

from paper_anchors import manifest_sources
from check_manifest import checked_source_pin

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "ledger" / "manifest.yaml"

STATEMENT_ENVS = ("theorem", "lemma", "proposition", "prop", "corollary")
LABEL_IN_STATEMENT = re.compile(
    r"\\begin\{(" + "|".join(STATEMENT_ENVS) + r")\}(?:\[[^\]]*\])?[^\\]*\\label\{([^}]+)\}")
# A node names the paper statement it transcribes as `(label <name>)`.  The
# paper's own labels are bare words (`the_theorem`), so a prefix cannot be
# required; the word `label` is what marks the name.
LABEL_TOKEN = re.compile(r"label\s+([A-Za-z][A-Za-z0-9:_-]*)")
# A statement the paper leaves unlabelled cannot be claimed by name, so a node
# claims it by line: the `source:` range must contain the line it opens on.
BEGIN_STATEMENT = re.compile(r"\\begin\{(" + "|".join(STATEMENT_ENVS) + r")\}")


def label_variants(label: str) -> list[str]:
    """A source may write `cor-derivative_bound` for `\\label{cor:derivative_bound}`."""
    out = [label]
    if "-" in label and ":" not in label:
        out.append(label.replace("-", ":", 1))
    return out


def paper_statements(text: str) -> list[tuple[str, int, str | None]]:
    """Identify theorem-like environments by kind, opening line, and optional label."""
    statements = []
    seen = set()
    for m in LABEL_IN_STATEMENT.finditer(text):
        if m.group(2) in seen:
            raise ValueError(f"duplicate statement label {m.group(2)!r}")
        seen.add(m.group(2))
        statements.append((m.group(1), text[:m.start()].count("\n") + 1, m.group(2)))
    labelled_lines = {line for _, line, _ in statements}
    for m in BEGIN_STATEMENT.finditer(text):
        line = text[:m.start()].count("\n") + 1
        if line in labelled_lines:
            continue
        statements.append((m.group(1), line, None))
    if not statements:
        raise ValueError("pinned source has no theorem-like statements")
    return sorted(statements, key=lambda statement: statement[1])


def uncovered_statements(text: str, filename: str, nodes: list[dict]) -> tuple[list, list]:
    """Compare one source only with theorem rows assigned to its exact pin."""
    claimed, ranges = set(), []
    source_range = re.compile(
        rf"(?:{re.escape(filename)}|{re.escape(Path(filename).name)}):"
        r"(\d+)(?:-(\d+))?")
    for node in nodes:
        if node["kind"] != "theorem":
            continue
        for label in LABEL_TOKEN.findall(node["source"]):
            claimed.update(label_variants(label))
        for span in source_range.finditer(node["source"]):
            ranges.append((int(span.group(1)), int(span.group(2) or span.group(1))))
    statements = paper_statements(text)
    uncovered = [statement for statement in statements
                 if (statement[2] not in claimed if statement[2] is not None
                     else not any(a <= statement[1] <= b for a, b in ranges))]
    return statements, uncovered


def allowed_gaps(manifest: dict, groups: dict) -> dict:
    """Read exact, source-bound gap allowances without accepting unknown or stale entries."""
    entries = manifest.get("coverage_allowed_gaps", [])
    if not isinstance(entries, list):
        raise ValueError("coverage_allowed_gaps must be a list")
    allowed = {}
    for entry in entries:
        if not isinstance(entry, dict) or set(entry) != {"source_pin", "reason", "statements"}:
            raise ValueError("each coverage gap entry needs source_pin, reason, and statements")
        if not isinstance(entry["reason"], str) or not entry["reason"].strip():
            raise ValueError("each coverage gap entry needs a nonempty reason")
        errors = []
        filename = checked_source_pin(entry["source_pin"], "coverage_allowed_gaps", errors)
        if errors or filename is None:
            raise ValueError("; ".join(errors))
        pin = entry["source_pin"]
        key = (filename, pin["sha256"])
        if key not in groups or pin != groups[key]["pin"]:
            raise ValueError("coverage allowance must select an exact active source pin")
        if key in allowed:
            raise ValueError(f"duplicate coverage allowance for {filename!r}")
        if not isinstance(entry["statements"], list) or not entry["statements"]:
            raise ValueError("coverage allowance statements must be a nonempty list")
        gaps = set()
        for gap in entry["statements"]:
            if not isinstance(gap, dict) or set(gap) != {"kind", "line", "label"}:
                raise ValueError("each allowed statement needs kind, line, and label")
            if gap["kind"] not in STATEMENT_ENVS or type(gap["line"]) is not int:
                raise ValueError("invalid allowed statement kind or line")
            if gap["line"] < 1 or (gap["label"] is not None and
                    (not isinstance(gap["label"], str) or not gap["label"])):
                raise ValueError("invalid allowed statement line or label")
            statement = (gap["kind"], gap["line"], gap["label"])
            if statement in gaps:
                raise ValueError("duplicate allowed statement")
            gaps.add(statement)
        allowed[key] = (gaps, entry["reason"])
    return allowed


def main() -> int:
    try:
        manifest = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))
        _, groups = manifest_sources(manifest)
        allowed = allowed_gaps(manifest, groups)
        selected = os.environ.get("EXPLODING_PAPER")
        if selected and not any((ROOT / key[0]).resolve() == Path(selected).resolve()
                                for key in groups):
            raise ValueError("EXPLODING_PAPER must name a registered exact source pin")
        # Coverage always checks every pin, even when a caller supplies a known path.
        partial, failed = False, False
        for key, group in groups.items():
            filename, digest = key
            statements, uncovered = uncovered_statements(
                (ROOT / filename).read_text(encoding="utf-8"), filename, group["nodes"])
            print(f"check_coverage: {filename} ({digest}): "
                  f"{len(statements) - len(uncovered)}/{len(statements)} statements claimed; "
                  f"{sum(n['kind'] == 'definition' for n in group['nodes'])} definitions "
                  "excluded from theorem coverage")
            expected, reason = allowed.get(key, (set(), ""))
            actual = set(uncovered)
            if actual:
                partial = True
                print("Not claimed by theorem rows under this exact source pin:")
                for kind, line, label in uncovered:
                    print(f"  {Path(filename).name}:{line}  {kind} "
                          f"{label or '(unlabelled)'}")
            if actual != expected:
                failed = True
                for kind, line, label in sorted(actual - expected, key=lambda item: item[1]):
                    print(f"  unexpected gap: {kind} at line {line}, {label!r}")
                for kind, line, label in sorted(expected - actual, key=lambda item: item[1]):
                    print(f"  stale gap allowance: {kind} at line {line}, {label!r}")
            elif actual:
                print(f"check_coverage: PARTIAL scope explicitly recorded: {reason}")
        if failed:
            print("check_coverage: FAIL (coverage differs from the explicit scope)",
                  file=sys.stderr)
            return 1
        if partial:
            print("check_coverage: OK within the explicit partial scopes; "
                  "whole-paper formalization is not certified")
        else:
            print("all numbered statements have theorem-row claims under their exact source pins; "
                  "independent statement and proof audits are still required")
        return 0
    except (OSError, ValueError, TypeError, yaml.YAMLError) as exc:
        print(f"check_coverage: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
