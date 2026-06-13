#!/usr/bin/env -S uv run
# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Translate one `define_air!` schema trace block into a `define_air_fns!`
opcode module.

The schema and the fn-DSL describe the same AIR; this converter performs the
mechanical rewrite (access-bundle expansion, derived -> let, constraints ->
constrain, lookups -> consume/emit) so the algebra is copied verbatim rather
than hand-retyped. The emitted module is reviewed before use.
"""

import re
import sys

BUNDLE = ["addr", "prev_0", "prev_1", "prev_2", "prev_3", "clock_prev",
          "next_0", "next_1", "next_2", "next_3"]


def split_top(s):
    """Split on top-level commas (depth-0 outside parens)."""
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur)
    return [x.strip() for x in out if x.strip()]


def section(block, name):
    """Extract the brace-delimited body of `name: { ... }` from block text."""
    i = block.index(name + ":")
    i = block.index("{", i)
    depth, j = 0, i
    while True:
        if block[j] == "{":
            depth += 1
        elif block[j] == "}":
            depth -= 1
            if depth == 0:
                break
        j += 1
    return block[i + 1:j]


def strip_comments(s):
    return "\n".join(
        line for line in s.splitlines() if not line.strip().startswith("//")
    )


def expand_committed(committed, bundles):
    cols = []
    for c in split_top(committed):
        if c in bundles:
            cols += [f"{c}_{suf}" for suf in BUNDLE]
        else:
            cols.append(c)
    return cols


def wrap_literals(arg):
    arg = arg.strip()
    if re.fullmatch(r"-?\d+", arg):
        return f"constant({arg})"
    return arg


def main():
    path, name, fn_name = sys.argv[1], sys.argv[2], sys.argv[3]
    bundles = sys.argv[4].split(",") if len(sys.argv) > 4 else []
    text = open(path).read()
    block = section(text, name)

    committed = strip_comments(section(block, "committed"))
    derived = strip_comments(section(block, "derived"))
    constraints = strip_comments(section(block, "constraints"))
    lookups = strip_comments(section(block, "lookups"))

    cols = expand_committed(committed, bundles)
    flags = [c for c in cols if re.fullmatch(r"opcode_\w+_flag", c)]
    enabler_sum = " + ".join(flags)

    def subst_enabler(s):
        return re.sub(r"\benabler\b", "row_enabler", s)

    lets = [f"let row_enabler = {enabler_sum};"]
    for d in split_top(derived):
        k, v = d.split(":", 1)
        lets.append(f"let {k.strip()} = {subst_enabler(v.strip())};")

    cons = [f"constrain {subst_enabler(c)};" for c in split_top(constraints)]

    relations = {}
    looks = []
    for entry in split_top(lookups):
        e = subst_enabler(entry).strip()
        # `batch: N` tunes LogUp fraction batching; the generated opcode
        # component already emits one fraction per entry, so it is a no-op here.
        if re.match(r"^batch\s*:", e):
            continue
        # Schema convention: a leading `-` means consume (negative
        # multiplicity); no sign means emit (positive multiplicity).
        sign = "+"
        if e[0] in "+-":
            sign = e[0]
            e = e[1:].strip()
        m = re.match(r"^(.*?)\*\s*(\w+)\s*\((.*)\)\s*$", e, re.S)
        mult = m.group(1).strip()
        rel = m.group(2)
        args = split_top(m.group(3))
        relations.setdefault(rel, len(args))
        args_s = ", ".join(wrap_literals(a) for a in args)
        verb = "consume" if sign == "-" else "emit"
        gate = "" if mult == "row_enabler" else f"({mult})"
        looks.append(f"{verb}{gate} {rel}({args_s});")

    rel_decls = "\n    ".join(f"relation {r}({a});" for r, a in relations.items())
    params = ",\n        ".join(cols)
    body = "\n        ".join(lets + [""] + cons + [""] + looks)

    print(f"""stwo_macros::define_air_fns! {{
    max_degree: 3,
    embedded: [],
    embedded_component: true,

    {rel_decls}

    fn {fn_name}(
        {params}
    ) {{
        {body}
        return pc;
    }}
}}""")


if __name__ == "__main__":
    main()
