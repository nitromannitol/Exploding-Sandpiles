#!/usr/bin/env python3
"""Write ASSUMPTIONS.md: every result this development assumes, with its statement.

A reader who is told that something is assumed should be able to see exactly
what. This lists FROZEN definitions in `Exploding/External/`, with where the
paper cites them and the verbatim Lean propositions that are assumed. FROZEN
definitions elsewhere are definitions stated separately, not cited results.

    python3 tools/assumptions.py            # write ASSUMPTIONS.md
    python3 tools/assumptions.py --check    # fail if the file on disk is stale
"""
import pathlib, re, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from check_manifest import strip_block_comments  # noqa: E402
from sync_docs import (is_cited_external, is_local_definition,
                       load_manifest, source_pins)  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent
BEGIN, END = "-- FROZEN-STATEMENT-BEGIN", "-- FROZEN-STATEMENT-END"


def frozen_block(path):
    t = (ROOT / path).read_text(encoding="utf-8")
    return t[t.index(BEGIN) + len(BEGIN):t.index(END)].strip("\n")


def companions(nodes):
    """Assumed propositions for which this repository also supplies a proof.

    The proof lives beside the proposition in a `*Proved.lean` companion; some
    prove it outright and some under hypotheses the paper's setting satisfies.
    """
    out = {}
    for n in nodes:
        if n.get("state") in ("SEALED", "PROVED") and n["file"].endswith("Proved.lean"):
            out[pathlib.Path(n["file"]).name[: -len("Proved.lean")]] = n
    return out


def bridge_proof(n):
    """A theorem outside `External/` and `Frozen/` whose type is exactly the assumed proposition.

    Such a theorem discharges the hypothesis unconditionally, wherever it lives (for example a
    `Bridge/` module proving the proposition from a library).
    """
    export = n["export"]
    short = export.split(".")[-1]
    names = {re.escape(export), r"External\." + re.escape(short)}
    pat = re.compile(r"^theorem\s+(\S+)\s*:\s*(?:" + "|".join(names) + r")\s*:=", re.M)
    pkg = pathlib.Path(n["file"]).parts[0]
    for f in sorted((ROOT / pkg).rglob("*.lean")):
        rel = f.relative_to(ROOT)
        if "External" in rel.parts or "Frozen" in rel.parts:
            continue
        text = f.read_text(encoding="utf-8")
        text = text.replace("-- FROZEN-STATEMENT-BEGIN", "").replace(
            "-- FROZEN-STATEMENT-END", "")
        m = pat.search(text)
        if m:
            return {"id": m.group(1), "file": str(rel)}
    return None


def _theorem_headers(text):
    """Yield `(name, binders, type, raw)` for each top-level `theorem` declaration.

    `binders` is the text between the name and the first top-level colon, `type` the text
    between that colon and the `:=` ending the header, and `raw` the whole header up to the
    `:=`.  `text` must have comments masked (pass it through `strip_block_comments`).
    """
    pattern = re.compile(
        r"(?m)^[ \t]*(?:noncomputable\s+|protected\s+|private\s+)*"
        r"theorem\s+([A-Za-z0-9_'.]+)")
    for m in pattern.finditer(text):
        name = m.group(1)
        i = m.end()
        depth = 0
        end = None
        j = i
        while j < len(text):
            ch = text[j]
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
            elif depth == 0 and text.startswith(":=", j):
                end = j
                break
            j += 1
        if end is None:
            continue
        header = text[i:end]
        depth = 0
        colon = None
        for k, ch in enumerate(header):
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
            elif ch == ":" and depth == 0:
                colon = k
                break
        if colon is None:
            continue
        binders = header[:colon].strip()
        typ = header[colon + 1:].strip()
        raw = f"theorem {name}{header}".rstrip()
        yield name, binders, typ, raw


def conditional_bridge_proof(n, externals, frozen_text):
    """A theorem outside `External/` and `Frozen/` that derives the assumed proposition from
    another registered external and is consumed by a frozen statement.

    Such a theorem discharges the hypothesis only under the other external, so it is reported
    as *proved here, under hypotheses* rather than as an outright proof.  Requiring that the
    name occurs in a frozen file keeps the note to the derivations the sealed surface uses.
    """
    export = n["export"]
    short = export.split(".")[-1]
    names = {export, "External." + short}
    pkg = pathlib.Path(n["file"]).parts[0]
    for f in sorted((ROOT / pkg).rglob("*.lean")):
        rel = f.relative_to(ROOT)
        if "External" in rel.parts or "Frozen" in rel.parts:
            continue
        text = strip_block_comments(f.read_text(encoding="utf-8"))
        for name, binders, typ, raw in _theorem_headers(text):
            if not binders or typ not in names:
                continue
            if not any(exp in binders for exp in externals):
                continue
            if re.search(r"\b" + re.escape(name) + r"\b", frozen_text) is None:
                continue
            return {"id": name, "file": str(rel), "conditional_statement": raw}
    return None


def conditional(c):
    """The frozen statement of a companion node, when it carries hypotheses; else None.

    A companion `theorem NAME : PROP` proves the assumed proposition outright.  One with
    binders proves it only under them (for example only on transient graphs), and the reader
    must see which, so its statement is shown beside the assumed one.
    """
    if "file" not in c or not c["file"].endswith("Proved.lean"):
        return None
    block = frozen_block(c["file"])
    body = re.sub(r"(?s)^\s*/--.*?-/\s*", "", block)
    if re.fullmatch(r"(?s)theorem\s+\S+\s*:\s*\S+\s*", body):
        return None
    # Show the statement only: a frozen block may also carry the proof after `:=`.
    return block.split(":=", 1)[0].rstrip()


def bridge_condition(c):
    """The statement displayed for a derived proof, conditional or not; None when the proof
    is unconditional (a `*Proved.lean` companion or an outright `bridge_proof`)."""
    if c.get("conditional_statement"):
        return c["conditional_statement"]
    return conditional(c)


def render():
    man = load_manifest(ROOT / "ledger" / "manifest.yaml")
    pins = source_pins(man["nodes"], man)
    assumed = [n for n in man["nodes"] if is_cited_external(n)]
    local_definitions = [n for n in man["nodes"] if is_local_definition(n)]
    mixed = bool(local_definitions)
    comp = companions(man["nodes"])
    out = ["# What this development assumes", ""]
    if not assumed:
        out += ["No cited inputs are declared as FROZEN definitions in `Exploding/External/`.",
                "This is a statement about the manifest, not a claim of complete paper coverage.",
                f"The manifest records {len(local_definitions)} definitions stated separately;",
                "they are not cited results.", ""]
        return "\n".join(out)
    out += [
        "The results below are quoted by the paper from the literature; the paper does",
        "not prove them.  Each is a proposition carried as an explicit hypothesis by",
        "every theorem whose proof uses it, so a theorem's statement shows which of",
        "these it takes as hypotheses.",
        "",
        f"There are {len(assumed)} of them.  Each entry gives the node id, where the paper",
        "cites the result, and the verbatim Lean proposition that is assumed.",
        "",
        "This file is generated by `python3 tools/assumptions.py` from",
        "`ledger/manifest.yaml` and the Lean sources; do not edit it by hand.",
        "",
    ]
    if mixed:
        names = ", ".join(f"`{n['id']}`" for n in local_definitions)
        out += [f"The manifest also records {len(local_definitions)} definitions stated separately"
                + (f": {names}." if local_definitions else "."),
                "They are not cited results. Each citation below gives the source file it is",
                "taken from.", ""]
    frozen_text = "\n".join(
        p.read_text(encoding="utf-8")
        for p in sorted((ROOT / "Exploding" / "Frozen").rglob("*.lean")))
    externals = {n["export"] for n in assumed}
    for n in assumed:
        stem = pathlib.Path(n["file"]).stem
        if stem in comp:
            continue
        b = bridge_proof(n)
        if b is None:
            b = conditional_bridge_proof(n, externals, frozen_text)
        if b:
            comp[stem] = b
    withproof = [n for n in assumed if pathlib.Path(n["file"]).stem in comp]
    if withproof:
        out += [(f"Of these, **{len(withproof)} are also proved in this repository** and so need not "
                 "be taken on trust; each is marked below with the theorem that proves it. "
                 if len(withproof) > 1 else
                 "Of these, **one is also proved in this repository** and so need not "
                 "be taken on trust; it is marked below with the theorem that proves it. ") +
                f"The remaining **{len(assumed) - len(withproof)}** "
                + ("is" if len(assumed) - len(withproof) == 1 else "are")
                + " assumed outright.", ""]
        ncond = sum(1 for n in withproof if bridge_condition(comp[pathlib.Path(n["file"]).stem]))
        if ncond:
            out[-2] += ((f" Of the {len(withproof)} proofs, **{ncond}** "
                         + ("holds only under hypotheses of its own, shown with it"
                            if ncond == 1 else
                            "hold only under hypotheses of their own, shown with them")
                         + "; where those fail, the result is still assumed.")
                        if len(withproof) > 1 else
                        (" That proof holds only under hypotheses of its own, shown with it; where "
                         "those fail, the result is still assumed."))
    for n in sorted(assumed, key=lambda x: x["id"]):
        c = comp.get(pathlib.Path(n["file"]).stem)
        cond = bridge_condition(c) if c else None
        if cond:
            line = (f"* **Also proved here, under hypotheses**, by `{c['id']}` in `{c['file']}`, "
                    "whose statement is shown after the assumed one; where those hypotheses "
                    "hold, this hypothesis can be discharged, and elsewhere it is assumed")
        elif c:
            line = (f"* **Also proved here** by `{c['id']}` in `{c['file']}`, so this hypothesis "
                    "can be discharged rather than assumed")
        else:
            line = "* **Not proved here**: this one is assumed outright"
        out += [f"## `{n['id']}`", "",
                f"* **Lean name** `{n['export']}`",
                f"* **File** `{n['file']}`",
                f"* **Cited at** {n['source']}",
                line,
                "",
                "```lean",
                frozen_block(n["file"]),
                "```",
                ""]
        if mixed:
            pin = pins[n["id"]]
            out += [f"Source: `{pin['file']}`, digest `{pin['sha256']}`.", ""]
        if cond:
            out += [f"The proof `{c['id']}`:", "", "```lean", cond, "```", ""]
    return "\n".join(out)


def main():
    try:
        text = render()
        target = ROOT / "ASSUMPTIONS.md"
        if "--check" in sys.argv[1:]:
            cur = target.read_text(encoding="utf-8") if target.exists() else ""
            if cur != text:
                print("assumptions: ASSUMPTIONS.md is stale; rerun tools/assumptions.py",
                      file=sys.stderr)
                return 1
            print("assumptions: OK (ASSUMPTIONS.md is current)")
        else:
            target.write_text(text, encoding="utf-8")
            n = text.count("\n## `")
            print(f"assumptions: wrote ASSUMPTIONS.md ({n} assumed result(s))")
    except (LookupError, KeyError, OSError, ValueError) as exc:
        print(f"assumptions: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
