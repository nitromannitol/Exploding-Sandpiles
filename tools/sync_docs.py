"""Regenerate the status block of README.md and the paper and manifest tables of CORRESPONDENCE.md.

Both documents restate what `ledger/manifest.yaml` already records: how many
nodes exist, what state each is in, and where in the paper each one comes from.
Restated facts go stale.  Everything between a BEGIN/END marker pair below is
generated from the manifest and the paper, so the prose in those files never
disagrees with the checkers.

    python3 tools/sync_docs.py            # check, exit 1 if a block is stale
    python3 tools/sync_docs.py --write    # regenerate the blocks in place
"""

from __future__ import annotations

import hashlib
import re
import sys
from collections import Counter
from pathlib import Path

try:
    import yaml
except ImportError:
    sys.exit("sync_docs.py: PyYAML is required (pip install pyyaml)")

from check_manifest import block_of, checked_source_pin, check_source_address, strip_block_comments

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "ledger" / "manifest.yaml"
PAPER = "exploding.tex"
PKG = "Exploding"
HISTORICAL_SOURCE = "paper/exploding.tex"
HISTORICAL_SHA256 = "1d7c2010d8bd29e7fb83e93f19c9ebe0e8aef201f93559b2b18f5ca0dc049b44"
# Declaration identities accompanying the historical correspondence annotations.
# A successor requires a fresh review; changing the manifest does not refresh a note.
HISTORICAL_DECLARATIONS = {
    "thm-limit-shape": (4, "7a9bc664298b2adfc0b528e3f1d6ba565efdcb2da1d055eb6e222032e835b44b"),
    "thm-time-constant": (5, "e2982ba6c4bcfa0f77bde5a780c388f19a53c0dea53751b01958d6d9bed8f8a1"),
    "thm-explosive": (3, "8132c02216ac6b502b1b4e6bb898ead2d8aaeea4a7b9da2795b1f83af4b403ed"),
    "prop-renormalization": (4, "79b4e8c59d8d852b23963f9f48ecd2a4c39a6d1e66163c3eaa41f57c08ade127"),
    "lem-square-lower-bound": (4, "ef7444fd525fb739159df1b1f18e6d7795f7028ca66531e1c9f675c3b15ab9b7"),
    "lem-penultimate-cluster": (4, "3cfbfa23e89ec1c52bed2c12a4a6be62d2cd17bb135b6f9438498d8f244d8544"),
    "lem-penultimate-upper-bound": (4, "755dc2bd6ea319253c74e38c3f0320cd0b6ec98d60157d330873710e2519e903"),
    "prop-last-wave-convergence": (4, "757cd6a770e4ea98496b4203ac93795842f3cbafac4b0ee55cea24e49f32e679"),
    "prop-approximate-subadditive": (4, "724f16a435a724da7cf5af101b9d248d41329ddd4286e2360a1502aa9f2138a4"),
    "prop-generalized-last-wave": (4, "63edbd1a3a9902f41df41c9c3efbe3e73ae7802ffacce176582e67f10b0cf8f3"),
    "thm-generalized-convergence": (5, "d81928d9c4ec6e2469184bd5c807767999597eacb970ea31d10a3458fd5f9e75"),
    "thm-counterexample": (3, "c9c8b8778d204a8280a899f7dda2fefda47e85854c1169bb477828b81f191dd3"),
    "prop-explosion-criteria": (3, "1346c0fe8b765d135baa9ad2b1a81e233decd87ad277bc353504f7b721b270ca"),
    "prop-box-crossing": (3, "d0e2daded00c514cd4ea1476eb509a9440219ff70994ebcc7fa6b1b58a9a0f1a"),
    "ext-fey-levine-peres": (3, "bb15c9367cd9630ab65ea5d4d6829aca3ced6da045c2f2e078edb1306a3f890c"),
    "ext-schonmann-bootstrap": (3, "26fb069d31c8b054743da77918174384ef4a3981145d075fda165b96748b51ce"),
    "ext-liggett-schonmann-stacey": (1, "60327e46178ffdfcf6edcdcc3590b2896f6ea1a0bdaf71064c3782d2e159cd96"),
    "ext-lss-bounded-degree": (1, "21027b6175c4669b5dd05dd0e6083e3f962b6df4955405b6ddf28305eaac4e4f"),
    "ext-antal-pisztora": (2, "952704b4ea136adac8cd89abdfdd69dedc9a57e4362d8f376117324a6bccbfb7"),
    "ext-mathieu-holes": (1, "0e80c60c71a1048803975b1b15f05e7eb37519bb878f00d7e6277d97a9581bb7"),
    "ext-fey-meester-redig": (1, "f834322e354be0f0fcbfbd64b3f9eaefbfadf4457ff510062932911d4f45e44b"),
    "lem-last-wave-bound": (3, "747c9a088fbc2cde832d7fb7842235dd0ba49396ddf1e67a96c5bed6e2872338"),
    "prop-dimensional-reduction": (3, "5777a520125b85ceccd832b9191d16da33405025e490edfaa05aa10b546da169"),
    "lem-approx-subadditivity": (3, "cc8f12ca936e4c7004662f4796489012419c44eb5071f5549ea1fa3cf5fc67f5"),
    "prop-recurrence": (3, "fb09b457811848161a746759e6fd31ee024a56bee43df4e23cca58af7ae87fa1"),
    "lem-local-convexity": (4, "c265b27336538e776144ad00d8ad3e44a93816312863f9b3cb9dc3d5997e91f4"),
    "lem-finite-exploding": (7, "70e35f646e03b599a40942113c9c6f1ad34cb35dc8757901a8ca990199169701"),
    "prop-crossing-time": (3, "86d88877abf5e6e1dc37f9bf5e1a1552bb04588de3fa050596b1faf4fb3d5e38"),
    "ext-fey-levine-peres-proved": (3, "a25c10e2f66ff0a1141aea2274ab888744e3a0a24b8e65077a671b3ea60ecb7a"),
    "ext-schonmann-bootstrap-proved": (3, "b2f9d167d3cbd4c150d94c771f06b6055ed809a62378fb549e2c0b7422c1ce89"),
    "ext-liggett-schonmann-stacey-proved": (3, "6e609b780ea329e70e990e77907f747ada26a64305328c08706a8485063f25a8"),
    "ext-lss-bounded-degree-proved": (3, "9aa2a465b3b5605a385b58bd5f10bd797dfe19b79ad879443b55c89edcec591c"),
    "ext-mathieu-holes-proved": (3, "a4e5f4c96380f1c0cb7ea3486a314a7a34642385542f07711499380586dc9c72"),
    "ext-fey-meester-redig-proved": (3, "07eb5a1029975901b972459f3aaf76af37efeaac0c826a5f606ed573367f7141"),
}
# Earlier reviewed identities of the two quoted results, stated for 0 < p < 1 before the
# endpoint p = 1 was added; an older manifest that still records one of them is accepted.
EARLIER_DECLARATIONS = {
    "ext-fey-levine-peres": (2, "16cbe44911cfe7e8ec9c4369cb757275bcb1d30cc51822c13f68488d34e7ca02"),
    "ext-schonmann-bootstrap": (2, "1ef132590c8069beea81e81b996ec77278f3f8614af4224fec242eb74c88e6de"),
}

SURFACE_BEGIN = "<!-- FROZEN-SURFACE-BEGIN (generated by tools/sync_docs.py) -->"
SURFACE_END = "<!-- FROZEN-SURFACE-END -->"
STATUS_BEGIN = "<!-- STATUS-BEGIN (generated by tools/sync_docs.py) -->"
STATUS_END = "<!-- STATUS-END -->"
MAP_BEGIN = "<!-- PAPER-MAP-BEGIN (generated by tools/sync_docs.py) -->"
MAP_END = "<!-- PAPER-MAP-END -->"

LABEL_RE = re.compile(r"label ([A-Za-z][A-Za-z0-9:_-]*)")
RANGE_RE = re.compile(re.escape(PAPER) + r":(\d+)(?:-(\d+))?")
CITED_RE = re.compile(r"(?:in the proof of|for) ([A-Za-z][A-Za-z0-9:_-]*)")

# How the paper numbers its statements: environment -> (printed name, counter).
# Environments sharing a counter share its name. Every counter except those in
# GLOBAL_COUNTERS is reset at each \section, as the paper's \newtheorem
# declarations say; `\newtheorem{remark}{Remark}` numbers remarks through the
# whole paper.
ENVIRONMENTS = {
    "theorem": ("Theorem", "theorem"),
    "lemma": ("Lemma", "theorem"),
    "prop": ("Proposition", "prop"),
    "conj": ("Conjecture", "conj"),
    "remark": ("Remark", "remark"),
}
GLOBAL_COUNTERS = {"remark"}

# One short description per node, in the paper's words where it has them.
DESCRIPTIONS = {
    "rem-sharp-planar-obstruction": "The least planar covering wave order is of order n² log(n+1)",
    "def-counterexample-threshold": "The explosion threshold M_η used in Theorem 6.1",
    "def-counterexample-pile": "The exploding pile η + M_η δ₀ used in Theorem 6.1",
    "def-counterexample-arrival": "The arrival time used in Theorem 6.1",
    "def-counterexample-support": "The rescaled toppled region used in Theorem 6.1",
    "ext-fey-levine-peres": "Explosion of the Bernoulli background (Fey, Levine and Peres), cited",
    "thm-limit-shape": "The rescaled toppled region converges to a convex domain",
    "thm-time-constant": "The rescaled arrival times converge",
    "thm-explosive": "A criterion for a product background to explode",
    "prop-crossing-time": "Large boxes are crossed quickly",
    "prop-renormalization": "The infinite cluster of good cubes",
    "lem-local-convexity": "A path of topplings fills its bounding rectangle",
    "lem-square-lower-bound": "A common eventual square-filling bound of order n^d, with n^2 log(n+1) in the plane",
    "lem-finite-exploding": "The last wave is well defined",
    "lem-last-wave-bound": "The complete last-wave bound and its exterior-of-interior clause at every time",
    "lem-approx-subadditivity": "Penultimate-cluster arrival times are subadditive",
    "lem-penultimate-cluster": "Penultimate clusters are polylogarithmically small",
    "lem-penultimate-upper-bound": "A linear upper bound on last-wave arrival times",
    "lem-penultimate-close": "Last-wave and penultimate-cluster arrival times are close",
    "prop-last-wave-convergence": "Convergence of the last wave",
    "prop-approximate-subadditive": "The last wave approximates the exploding sandpile",
    "prop-generalized-last-wave": "Convergence of the last wave under the general hypotheses",
    "thm-generalized-convergence": "Convergence of the exploding sandpile under the general hypotheses",
    "thm-counterexample": "Explosive backgrounds without a limit shape",
    "prop-explosion-criteria": "A criterion for a background law to explode",
    "prop-dimensional-reduction": "Dimension reduction for every Boolean boundary field",
    "prop-recurrence": "The constant background d is recurrent",
    "ext-schonmann-bootstrap": "Schonmann's bound for bootstrap percolation, cited",
    "ext-liggett-schonmann-stacey":
        "Domination of a finitely dependent field by a product measure (Liggett, Schonmann and Stacey), cited",
    "ext-lss-bounded-degree":
        "Domination by a product measure on a dependence graph of bounded degree (Liggett, Schonmann and Stacey), cited",
    "ext-antal-pisztora": "The chemical distance in supercritical bond percolation (Antal and Pisztora), cited",
    "ext-mathieu-holes": "The holes of the infinite cluster of site percolation (Mathieu), cited",
    "ext-fey-meester-redig": "The least action principle (Fey, Meester and Redig), cited",
    "ext-fey-levine-peres-proved": "In-repo discharge of the Fey, Levine and Peres explosion theorem",
    "ext-schonmann-bootstrap-proved": "In-repo discharge of Schonmann's bootstrap bound",
    "ext-liggett-schonmann-stacey-proved": "In-repo discharge of the Liggett, Schonmann and Stacey domination theorem",
    "ext-lss-bounded-degree-proved": "In-repo discharge of the bounded-degree Liggett, Schonmann and Stacey corollary",
    "ext-mathieu-holes-proved": "In-repo discharge of Mathieu's hole-volume bound",
    "ext-fey-meester-redig-proved": "In-repo discharge of the Fey, Meester and Redig least action principle",
    "prop-box-crossing": "Product-law box crossing and the separate arbitrary-law dimension-one case",
    "ext-fey-den-boer-redig-cubical-cluster": "Cubical toppled support and lower radius, cited and unproved",
    "ext-fey-levine-peres-radius": "Upper radius of the ordinary pile, cited and unproved",
}

# The order in which states are reported, and what each one means.
STATE_ORDER = ["SEALED", "PROVED", "CONDITIONAL", "FROZEN", "DRAFT_SORRY"]
STATE_WORDS = {
    "SEALED": "proved here",
    "PROVED": "proved here",
    "CONDITIONAL": "proofs written that rest on open statements",
    "FROZEN": "cited results carried as hypotheses",
    "DRAFT_SORRY": "open",
}
STATE_CELL = {
    "SEALED": "proved",
    "PROVED": "proved",
    "CONDITIONAL": "proof written; rests on open statements",
    "FROZEN": "cited result, hypothesis",
    "DRAFT_SORRY": "open",
}


def load_nodes() -> list[dict]:
    return load_manifest()["nodes"]


def load_manifest(path: Path | None = None) -> dict:
    manifest = yaml.safe_load((path or MANIFEST).read_text(encoding="utf-8"))
    if not isinstance(manifest, dict) or not isinstance(manifest.get("nodes"), list):
        raise LookupError("manifest must contain a nodes list")
    if not manifest["nodes"]:
        raise LookupError("manifest contains no nodes")
    return manifest


def source_pins(nodes: list[dict], manifest: dict) -> dict[str, dict]:
    """Validate the default and every override before using their source identities."""
    errors: list[str] = []
    default = manifest.get("source_pin")
    checked_source_pin(default, "manifest", errors)
    result = {}
    for node in nodes:
        pin = node.get("source_pin", default)
        filename = checked_source_pin(pin, node["id"], errors)
        if filename is not None:
            check_source_address(node, filename, errors)
            result[node["id"]] = {**pin, "file": filename}
    if errors:
        raise LookupError("; ".join(errors))
    return result


def is_cited_external(node: dict) -> bool:
    """Only FROZEN definitions in the External directory denote cited inputs."""
    return (node.get("state") == "FROZEN" and node.get("kind") == "definition"
            and Path(node["file"]).parts[:2] == (PKG, "External"))


def is_local_definition(node: dict) -> bool:
    """Classify by registration location, without a source or literal-body verdict."""
    return (node.get("state") == "FROZEN" and node.get("kind") == "definition"
            and not is_cited_external(node))


def is_historical_source(pin: dict) -> bool:
    return pin["file"] == HISTORICAL_SOURCE and pin["sha256"] == HISTORICAL_SHA256


def legacy_reporting(nodes: list[dict], pins: dict[str, dict]) -> bool:
    return (all(is_historical_source(pins[n["id"]]) for n in nodes)
            and not any(is_local_definition(n) for n in nodes))


def source_range(node: dict, pin: dict) -> tuple[int, int]:
    filename = pin["file"]
    names = "|".join(re.escape(name) for name in (filename, Path(filename).name))
    match = re.search(r"(?<![A-Za-z0-9_./-])(?:" + names + r"):(\d+)(?:-(\d+))?",
                      node["source"])
    if match is None:
        raise LookupError(f"{node['id']}: no line address for pinned {filename}")
    return int(match.group(1)), int(match.group(2) or match.group(1))


def historical_audit_nodes(
        nodes: list[dict], pins: dict[str, dict]) -> tuple[list[dict], list[tuple[str, str]]]:
    """Existing hand-written audit notes apply only to their original source bytes."""
    eligible, excluded = [], []
    for node in nodes:
        pin = pins[node["id"]]
        if not is_historical_source(pin):
            excluded.append((node["id"], f"different source pin: {pin['file']} ({pin['sha256']})"))
        elif is_local_definition(node):
            excluded.append((node["id"], "non-External FROZEN definition; source/body check required"))
        elif not re.search(r"\.tex:\d+-\d+", node["source"]):
            excluded.append((node["id"], "citation has no explicit statement line range"))
        else:
            check_historical_declaration(node)
            eligible.append(node)
    return eligible, excluded


def check_historical_declaration(node: dict) -> None:
    """Reject reuse of a historical annotation for a changed frozen declaration."""
    nid = node["id"]
    expected = HISTORICAL_DECLARATIONS.get(nid)
    identity = (node.get("version"), node.get("frozen_sha256"))
    if (expected is None or type(node.get("version")) is not int
            or identity not in (expected, EARLIER_DECLARATIONS.get(nid))):
        raise LookupError(f"{nid}: historical annotation identity mismatch; fresh review required")
    expected = identity
    path = ROOT / node["file"]
    errors: list[str] = []
    got = block_of(path.read_text(encoding="utf-8"), path, errors)
    if got is None:
        raise LookupError("; ".join(errors))
    actual = hashlib.sha256(got[0].encode("utf-8")).hexdigest()
    if actual != expected[1]:
        raise LookupError(f"{nid}: actual frozen block differs from historical annotation; "
                          "fresh review required")


def lean_link(node: dict) -> str:
    """Link to the declaration itself, keeping line numbers derived data."""
    text = (ROOT / node["file"]).read_text(encoding="utf-8")
    matches = list(re.finditer(
        rf"^[ \t]*(?:noncomputable[ \t]+)?(?:theorem|def|abbrev|structure)\s+"
        rf"{re.escape(node['export'])}(?=\s|\{{|\(|:)",
        strip_block_comments(text), re.M))
    if len(matches) != 1:
        raise LookupError(f"expected one declaration of {node['export']}")
    line = text.count("\n", 0, matches[0].start()) + 1
    return f"[{node['export']}]({node['file']}#L{line})"


def paper_environments(filename: str = HISTORICAL_SOURCE) -> list[dict]:
    """Every numbered statement of the paper, with its printed number and span.

    Lines between `\\iffalse` and its `\\fi` are not typeset and are skipped."""
    lines = (ROOT / filename).read_text(encoding="utf-8").splitlines()
    envs, open_envs, counters, section, hidden = [], [], Counter(), 0, 0
    begin = re.compile(r"\\begin\{(" + "|".join(ENVIRONMENTS) + r")\}")
    for i, raw in enumerate(lines, start=1):
        line = re.sub(r"(?<!\\)%.*", "", raw)
        if re.match(r"\s*\\iffalse(?![A-Za-z])", line):
            hidden += 1
            continue
        if hidden:
            if re.match(r"\s*\\fi(?![A-Za-z])", line):
                hidden -= 1
            continue
        if re.search(r"\\section\*?\{", line):
            section += 1
            for counter in [c for c in counters if c not in GLOBAL_COUNTERS]:
                del counters[counter]
        m = begin.search(line)
        if m:
            name, counter = ENVIRONMENTS[m.group(1)]
            counters[counter] += 1
            number = (f"{counters[counter]}" if counter in GLOBAL_COUNTERS
                      else f"{section}.{counters[counter]}")
            label = re.search(r"\\label\{([^}]*)\}", line[m.end():])
            env = dict(kind=m.group(1), name=f"{name} {number}",
                       start=i, end=None, label=label.group(1) if label else None)
            envs.append(env)
            open_envs.append(env)
        for kind in re.findall(r"\\end\{(" + "|".join(ENVIRONMENTS) + r")\}", line):
            for env in reversed(open_envs):
                if env["kind"] == kind:
                    env["end"] = i
                    open_envs.remove(env)
                    break
    return envs


def paper_statement(node: dict, envs: list[dict], pin: dict | None = None) -> dict:
    """The numbered statement containing the first line the node cites."""
    first, _ = source_range(node, pin or {"file": HISTORICAL_SOURCE})
    inside = [e for e in envs if e["start"] <= first <= (e["end"] or e["start"])]
    if inside:
        return inside[-1]
    # A cited result is quoted inside a proof or in the text before a statement;
    # its source then names that statement's label.
    cited = CITED_RE.search(node["source"])
    if cited:
        named = [e for e in envs if e["label"] == cited.group(1)]
        if named:
            return named[0]
    raise LookupError(f"{node['id']}: line {first} is in no numbered statement")


def surface_table(nodes: list[dict], pins: dict[str, dict] | None = None) -> str:
    pins = pins if pins is not None else source_pins(nodes, load_manifest())
    if not legacy_reporting(nodes, pins):
        rows = ["| id | Lean | paper | source file | state |", "|---|---|---|---|---|"]
        for n in nodes:
            pin = pins[n["id"]]
            state = state_cell(n)
            rows.append(f"| `{n['id']}` | {lean_link(n)} | {n['source']} | "
                        f"`{pin['file']}` (`{pin['sha256'][:16]}`) | {state} |")
        return "\n".join(rows)
    rows = ["| id | Lean | paper | state |", "|---|---|---|---|"]
    for n in nodes:
        rows.append(f"| `{n['id']}` | {lean_link(n)} | {n['source']} | {n['state']} |")
    return "\n".join(rows)


def state_cell(node: dict) -> str:
    return ("definition" if is_local_definition(node)
            else STATE_CELL[node["state"]])


def source_status(nodes: list[dict], pins: dict[str, dict]) -> str:
    """Report declarations from several sources without turning them into whole-paper credit."""
    counts = Counter(n["state"] for n in nodes)
    unknown = set(counts) - set(STATE_ORDER)
    if unknown:
        raise LookupError(f"unknown node states {sorted(unknown)}")
    cited = sum(is_cited_external(n) for n in nodes)
    local_definitions = sum(is_local_definition(n) for n in nodes)
    proved_all = counts["SEALED"] + counts["PROVED"]
    parts = [f"{proved_all} proved"] if proved_all else []
    parts += [f"{counts[s]} {STATE_CELL[s]}" for s in ("CONDITIONAL", "DRAFT_SORRY") if counts[s]]
    if cited:
        parts.append(f"{cited} cited results")
    if local_definitions:
        parts.append(f"{local_definitions} definitions")
    if counts["FROZEN"] != cited + local_definitions:
        raise LookupError("a FROZEN node is neither a cited input nor a non-External definition")
    rows = [f"Status: **{len(nodes)} statements: {'; '.join(parts)}.**",
            "", "Each statement is taken from one source file. For each source the table "
            "gives its theorem statements, how many of them are proved, the cited results "
            "stated as hypotheses, and the definitions stated separately.", "",
            "| Source | SHA-256 | Theorem statements | Proved | Cited results | Definitions |",
            "|---|---|---|---|---|---|"]
    groups: dict[tuple[str, str], list[dict]] = {}
    for node in nodes:
        pin = pins[node["id"]]
        groups.setdefault((pin["file"], pin["sha256"]), []).append(node)
    for (filename, digest), group in sorted(groups.items()):
        theorems = [n for n in group if n.get("kind") == "theorem"]
        proved = sum(n["state"] in {"SEALED", "PROVED"} for n in theorems)
        rows.append(f"| [{filename}]({filename}) | `{digest}` | {len(theorems)} | {proved} | "
                    f"{sum(is_cited_external(n) for n in group)} | "
                    f"{sum(is_local_definition(n) for n in group)} |")
    rows += ["", "A cited result is a hypothesis of the theorems that use it, not an axiom "
             "(see ASSUMPTIONS.md). Definitions are not counted as theorems. These counts are "
             "generated from `ledger/manifest.yaml` by `python3 tools/sync_docs.py`; "
             "`python3 tools/check_axioms.py` checks the axiom closures."]
    return "\n".join(rows)


def status_block(nodes: list[dict], pins: dict[str, dict] | None = None) -> str:
    pins = pins if pins is not None else source_pins(nodes, load_manifest())
    if not legacy_reporting(nodes, pins):
        return source_status(nodes, pins)
    counts = Counter(n["state"] for n in nodes)
    unknown = set(counts) - set(STATE_ORDER)
    if unknown:
        raise LookupError(f"unknown node states {sorted(unknown)}")
    parts = [f"{counts[s]} `{s}`, {STATE_WORDS[s]}" for s in STATE_ORDER if counts[s]]
    if len(parts) == 1:
        head = parts[0]
    elif len(parts) == 2:
        head = f"{parts[0]}, and {parts[1]}"
    else:
        head = "; ".join(parts[:-1]) + "; and " + parts[-1]

    def ids(state: str) -> str:
        names = [f"`{n['id']}`" for n in nodes if n["state"] == state]
        if len(names) < 3:
            return " and ".join(names)
        return ", ".join(names[:-1]) + " and " + names[-1]

    body = []
    proved = counts["SEALED"] + counts["PROVED"]
    if proved:
        body.append(
            f"The {proved} proved statements are machine-checked, and each one's axiom\n"
            f"closure is exactly Lean's three standard axioms `propext`,\n"
            f"`Classical.choice` and `Quot.sound`.")
    if counts["CONDITIONAL"]:
        body.append(
            f"The {counts['CONDITIONAL']} `CONDITIONAL` statements, {ids('CONDITIONAL')}, have\n"
            f"complete proofs that use statements still open, so their axiom closures\n"
            f"contain `sorryAx` until those are proved.")
    if counts["FROZEN"]:
        body.append(
            f"The {counts['FROZEN']} `FROZEN` statements, {ids('FROZEN')}, are cited results,\n"
            f"stated in `{PKG}/External/` and carried as explicit hypotheses by the\n"
            f"theorems that use them; those theorems do not prove them, and ASSUMPTIONS.md\n"
            f"marks which are also proved elsewhere in this repository.")
    if counts["DRAFT_SORRY"]:
        body.append(
            f"Still open: {ids('DRAFT_SORRY')}.  Each has a frozen statement and a\n"
            f"proof that is a single `sorry`.")
    else:
        body.append("No node is open.")
    closing = (
        "Run `python3 tools/check_axioms.py` to see the axiom closure of every node;\n"
        "it fails while any closure contains `sorryAx`.  These counts are generated\n"
        "from `ledger/manifest.yaml` by `python3 tools/sync_docs.py`.")
    return (f"Status: **{len(nodes)} statements: {head}.**  "
            + "  ".join(body) + "  " + closing)


def paper_map(nodes: list[dict], pins: dict[str, dict] | None = None) -> str:
    """Link every registered statement to the paper statement it transcribes."""
    pins = pins if pins is not None else source_pins(nodes, load_manifest())
    if not legacy_reporting(nodes, pins):
        return source_paper_map(nodes, pins)
    envs = paper_environments()
    rows = ["| Paper result | Description | Lean statement | State |",
            "|---|---|---|---|"]
    entries = []
    for n in nodes:
        env = paper_statement(n, envs)
        label = f"<br>`{env['label']}`" if env["label"] else ""
        cell = f"[{env['name']}](paper/{PAPER}#L{env['start']}){label}"
        desc = DESCRIPTIONS[n["id"]]
        entries.append(((env["start"], int(RANGE_RE.search(n["source"]).group(1))),
                        f"| {cell} | {desc} | {lean_link(n)} | {STATE_CELL[n['state']]} |"))
    rows.extend(row for _, row in sorted(entries, key=lambda entry: entry[0]))
    return "\n".join(rows)


def source_paper_map(nodes: list[dict], pins: dict[str, dict]) -> str:
    rows = ["| Source | Paper statement or definition | Description | Lean declaration | State |",
            "|---|---|---|---|---|"]
    environments = {filename: paper_environments(filename)
                    for filename in {pin["file"] for pin in pins.values()}}
    entries = []
    for node in nodes:
        pin = pins[node["id"]]
        first, last = source_range(node, pin)
        filename = pin["file"]
        if is_local_definition(node):
            cell = f"[Definition, lines {first}-{last}]({filename}#L{first})"
            description = DESCRIPTIONS.get(node["id"], "A definition stated separately")
        else:
            env = paper_statement(node, environments[filename], pin)
            label = f"<br>`{env['label']}`" if env["label"] else ""
            cell = f"[{env['name']}]({filename}#L{env['start']}){label}"
            description = DESCRIPTIONS.get(node["id"], node["export"])
        row = (f"| `{filename}` | {cell} | {description} | {lean_link(node)} | "
               f"{state_cell(node)} |")
        entries.append(((filename, first, node["id"]), row))
    rows.extend(row for _, row in sorted(entries))
    return "\n".join(rows)


def splice(text: str, begin: str, end: str, body: str) -> str:
    i, j = text.find(begin), text.find(end)
    if i < 0 or j < 0:
        raise LookupError(f"missing marker pair {begin!r}")
    return text[:i] + begin + "\n\n" + body + "\n\n" + text[j:]


def main() -> int:
    write = "--write" in sys.argv[1:]
    try:
        manifest = load_manifest()
        nodes = manifest["nodes"]
        pins = source_pins(nodes, manifest)
        targets = [
            (ROOT / "CORRESPONDENCE.md", SURFACE_BEGIN, SURFACE_END, surface_table(nodes, pins)),
            (ROOT / "README.md", STATUS_BEGIN, STATUS_END, status_block(nodes, pins)),
            (ROOT / "CORRESPONDENCE.md", MAP_BEGIN, MAP_END, paper_map(nodes, pins)),
        ]
    except (LookupError, KeyError, OSError, ValueError) as exc:
        print(f"sync_docs: {exc}", file=sys.stderr)
        return 2

    original, updated = {}, {}
    for path, begin, end, body in targets:
        if "\u2014" in body or "\u2013" in body:
            print(f"sync_docs: a generated block of {path.name} contains a dash",
                  file=sys.stderr)
            return 2
        if path not in original:
            original[path] = path.read_text(encoding="utf-8")
        text = updated.get(path, original[path])
        try:
            updated[path] = splice(text, begin, end, body)
        except LookupError as exc:
            print(f"sync_docs: {path.name}: {exc}", file=sys.stderr)
            return 2

    stale = [(path, want) for path, want in updated.items() if want != original[path]]

    if not stale:
        print(f"sync_docs: OK ({len(nodes)} nodes; README.md and "
              f"CORRESPONDENCE.md agree with the manifest)")
        return 0

    for path, want in stale:
        print(f"  stale: {path.relative_to(ROOT)}")
        if write:
            path.write_text(want, encoding="utf-8")

    if not write:
        print("\nsync_docs: rerun with --write to regenerate", file=sys.stderr)
        return 1
    print(f"\nsync_docs: regenerated {len(stale)} file(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
