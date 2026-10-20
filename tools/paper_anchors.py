#!/usr/bin/env python3
"""Check (or repair) the paper line ranges recorded in ledger/manifest.yaml.

Each manifest node names the paper statement it formalizes as

    source: exploding.tex:<a>-<b> (label <lab>[, ...])

The line range is derived data: it is the span of the LaTeX environment that
contains `\\label{<lab>}`.  Editing the paper anywhere above a statement shifts
that span, so the recorded range goes stale silently.  The label itself is
stable, so this tool recomputes every range from its label and reports drift.

    python3 tools/paper_anchors.py            # check, exit 1 on drift
    python3 tools/paper_anchors.py --fix      # rewrite the stale source: lines

Nodes whose `source:` names no paper label are skipped.
Only statements under the default source file are re-anchored. Statements tied
to other sources are listed explicitly and require separate anchor review.
"""

from __future__ import annotations

import os
import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    sys.exit("paper_anchors.py: PyYAML is required (pip install pyyaml)")

from check_manifest import checked_source_pin, check_source_address

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "ledger" / "manifest.yaml"
LABEL_RE = re.compile(r"label\s+([A-Za-z][A-Za-z0-9:_-]*)")
BEGIN_RE = re.compile(r"\\begin\{([A-Za-z*]+)\}")
END_RE = re.compile(r"\\end\{([A-Za-z*]+)\}")

# Environments that carry a statement we would ever anchor to.
ANCHORABLE = {
    "theorem", "lemma", "proposition", "prop", "corollary", "definition", "remark",
    "problem", "conj",
    "equation", "equation*", "align", "align*", "gather", "gather*",
}

# A node that formalizes one clause of a multi-clause statement records the
# lines of its own clause, which sit inside the environment the label anchors.
# Its source says so, and such a node is checked for containment, not equality.
PART_RE = re.compile(r"\bpart\b|\bclause\b|\bcontext\b")


def manifest_sources(manifest: dict) -> tuple[tuple[str, str], dict]:
    """Validate effective exact source pins and partition their manifest rows."""
    if not isinstance(manifest, dict):
        raise ValueError("manifest must be a mapping")
    errors: list[str] = []
    default = manifest.get("source_pin")
    filename = checked_source_pin(default, "manifest", errors)
    if errors or filename is None:
        raise ValueError("; ".join(errors))
    default_key = (filename, default["sha256"])
    groups = {default_key: {"pin": default, "nodes": []}}
    nodes = manifest.get("nodes")
    if not isinstance(nodes, list) or not nodes:
        raise ValueError("manifest nodes must be a nonempty list")
    ids, files = set(), set()
    for node in nodes:
        if not isinstance(node, dict) or not isinstance(node.get("id"), str) or not node["id"]:
            raise ValueError("each manifest node must have a string id")
        nid = node["id"]
        if nid in ids:
            errors.append(f"duplicate node id {nid!r}")
        ids.add(nid)
        file = node.get("file")
        if not isinstance(file, str) or not file:
            errors.append(f"{nid}: declaration file is missing")
        else:
            relative = Path(file)
            resolved = (ROOT / relative).resolve()
            if (relative.is_absolute() or ".." in relative.parts or
                    ROOT.resolve() not in resolved.parents):
                errors.append(f"{nid}: declaration file must stay inside the repository")
            elif resolved in files:
                errors.append(f"{nid}: duplicate declaration file {file!r}")
            else:
                files.add(resolved)
        if node.get("kind") not in {"theorem", "definition"}:
            errors.append(f"{nid}: unknown declaration kind")
        pin = node.get("source_pin", default)
        selected = filename if pin == default else checked_source_pin(pin, nid, errors)
        if selected is None:
            continue
        key = (selected, pin["sha256"])
        if key in groups and groups[key]["pin"] != pin:
            errors.append(f"{nid}: inconsistent source pins for {selected!r}")
        groups.setdefault(key, {"pin": pin, "nodes": []})["nodes"].append(node)
        check_source_address(node, selected, errors)
    if errors:
        raise ValueError("; ".join(errors))
    return default_key, groups


def default_source_scope(manifest: dict) -> tuple[tuple[str, str], dict]:
    """Select the validated default source; reject an unrelated environment override."""
    default_key, groups = manifest_sources(manifest)
    if not groups[default_key]["nodes"]:
        raise ValueError("default source scope has no manifest rows")
    selected = os.environ.get("EXPLODING_PAPER")
    if selected and Path(selected).resolve() != (ROOT / default_key[0]).resolve():
        raise ValueError("EXPLODING_PAPER must select the manifest's default pinned source")
    return default_key, groups


def report_source_scope(tool: str, default_key: tuple[str, str], groups: dict) -> None:
    """Name the checked source and every row outside that explicit scope."""
    print(f"{tool}: source scope {default_key[0]} ({default_key[1]})")
    for key, group in groups.items():
        if key != default_key:
            excluded = ", ".join(node["id"] for node in group["nodes"])
            print(f"{tool}: excluded {len(group['nodes'])} rows from {key[0]} "
                  f"({key[1]}): {excluded}; anchors require separate source review")


def label_variants(label: str) -> list[str]:
    """The spellings a recorded label may have in the paper.

    A node id is written with hyphens because a colon reads badly in an id, so
    a source line may carry `cor-derivative_bound` where the paper writes
    `\\label{cor:derivative_bound}`.  The two name the same statement.
    """
    out = [label]
    if "-" in label and ":" not in label:
        out.append(label.replace("-", ":", 1))
    return out


def span_of_label(lines: list[str], label: str) -> tuple[int, int]:
    """1-indexed inclusive span of the environment containing \\label{label}."""
    text = "\n".join(lines)
    for cand in label_variants(label):
        if text.count(f"\\label{{{cand}}}") == 1:
            label = cand
            break
    marker = f"\\label{{{label}}}"
    hits = [i for i, line in enumerate(lines) if marker in line]
    if len(hits) != 1:
        raise LookupError(f"label {label!r} occurs {len(hits)} times, want 1")
    at = hits[0]

    # Walk up to the innermost enclosing anchorable \begin, tracking depth so a
    # nested environment that closes above us is not mistaken for our opener.
    depth = 0
    start = None
    for i in range(at, -1, -1):
        for env in END_RE.findall(lines[i]):
            if i != at and env in ANCHORABLE:
                depth += 1
        for env in BEGIN_RE.findall(lines[i]):
            if env not in ANCHORABLE:
                continue
            if depth:
                depth -= 1
            else:
                start = (i, env)
                break
        if start:
            break
    if start is None:
        raise LookupError(f"label {label!r} is not inside an anchorable environment")

    i0, env = start
    depth = 0
    for j in range(i0 + 1, len(lines)):
        if re.search(rf"\\begin\{{{re.escape(env)}\}}", lines[j]):
            depth += 1
        if re.search(rf"\\end\{{{re.escape(env)}\}}", lines[j]):
            if depth:
                depth -= 1
            else:
                return i0 + 1, j + 1
    raise LookupError(f"environment {env} opened at line {i0 + 1} never closes")


def main() -> int:
    fix = "--fix" in sys.argv[1:]
    try:
        manifest = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))
        default_key, groups = default_source_scope(manifest)
    except (OSError, ValueError, TypeError, yaml.YAMLError) as exc:
        print(f"paper_anchors: {exc}", file=sys.stderr)
        return 2
    report_source_scope("paper_anchors", default_key, groups)
    paper = ROOT / default_key[0]
    lines = paper.read_text(encoding="utf-8").splitlines()
    source_re = re.compile(
        rf"^(?:{re.escape(default_key[0])}|{re.escape(paper.name)}):"
        r"(?P<a>\d+)-(?P<b>\d+)\s*(?P<rest>.*)$")

    drift: list[tuple[str, str, str]] = []
    skipped = 0
    checked = 0
    for node in groups[default_key]["nodes"]:
        nid, source = node["id"], node["source"]
        label_match = LABEL_RE.search(source)
        if not label_match:
            skipped += 1
            continue
        label = label_match.group(1)
        try:
            a, b = span_of_label(lines, label)
        except LookupError as exc:
            drift.append((nid, source, f"UNRESOLVABLE: {exc}"))
            continue
        checked += 1
        got = source_re.match(source)
        address = source[:source.index(":")]
        want = f"{address}:{a}-{b}"
        if got:
            ga, gb = int(got.group("a")), int(got.group("b"))
            if (ga, gb) == (a, b):
                continue
            # A clause node records its own lines inside the anchored span.
            if PART_RE.search(source) and a <= ga <= gb <= b:
                continue
        rest = got.group("rest") if got else source[source.find("("):]
        drift.append((nid, source, f"{want} {rest}".strip()))

    if not drift:
        print(f"paper_anchors: OK ({checked} anchors resolved, "
              f"{skipped} nodes carry no paper label)")
        return 0

    for nid, old, new in drift:
        print(f"  {nid}\n    was: {old}\n    now: {new}")

    if not fix:
        print(f"\npaper_anchors: {len(drift)} stale anchor(s); rerun with --fix",
              file=sys.stderr)
        return 1

    text = MANIFEST.read_text(encoding="utf-8")
    for nid, old, new in drift:
        if new.startswith("UNRESOLVABLE"):
            print(f"paper_anchors: cannot repair {nid}", file=sys.stderr)
            return 1
        entry_start = re.search(rf"(?m)^  - id: {re.escape(nid)}\s*$", text)
        if entry_start is None:
            print(f"paper_anchors: no verbatim entry for {nid}", file=sys.stderr)
            return 1
        following = re.search(r"(?m)^  - id: ", text[entry_start.end():])
        entry_end = entry_start.end() + following.start() if following else len(text)
        entry = text[entry_start.start():entry_end]
        before = f"    source: {old}\n"
        if entry.count(before) != 1:
            print(f"paper_anchors: no verbatim source line for {nid}", file=sys.stderr)
            return 1
        replacement = entry.replace(before, f"    source: {new}\n", 1)
        text = text[:entry_start.start()] + replacement + text[entry_end:]
    MANIFEST.write_text(text, encoding="utf-8")
    print(f"\npaper_anchors: repaired {len(drift)} anchor(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
