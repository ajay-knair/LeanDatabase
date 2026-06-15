#!/usr/bin/env python3
"""Scaffold a CrossSkill equivalence example from the dataset.

Usage:
    python3 Examples/CrossSkill/scaffold.py <instance_id> [--force] [--tables T1,T2]

Reads Examples/crossskill_equivalent_sql.jsonl, finds <instance_id>, and writes
Examples/CrossSkill/<Id>.lean containing:
  - imports + `open LeanDatabase`
  - a docstring with the NL question and ALL equivalent SQL variants
  - for every table the queries reference: the FULL schema (every column from the
    DDL) as `<Table>CT`, its DecidableEq instance, and one projection per column
  - a theorem skeleton ending in `:= by sql_equiv`

Then you fill in the query `def`s and (if needed) tweak the proof by hand.
The point of emitting EVERY column (not just the ones used) is to check that a
large dependent schema doesn't choke `sql_equiv`.
"""
import json, re, sys, os

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "crossskill_equivalent_sql.jsonl")

LEAN_KEYWORDS = {
    "end","then","else","do","by","fun","let","in","at","if","calc","match","with",
    "from","have","show","this","where","deriving","class","instance","structure",
    "def","theorem","example","variable","open","namespace","section","set","mut",
}

def sql_proxy(sql_type: str) -> str:
    """Mirror LeanDatabase.Parser.sqlProxy: DDL type -> SQLTypeProxy constructor."""
    s = sql_type.lower()
    starts = lambda *ps: any(s.startswith(p) for p in ps)
    if starts("varchar","text","char","string"):         return ".string"
    if starts("bool"):                                    return ".bool"
    if starts("float","double","real"):                   return ".float"
    if starts("int","number","numeric","decimal","bigint","smallint","tinyint"): return ".int"
    if starts("date","timestamp","time"):                 return ".string"   # dates modeled as strings
    return ".string"   # default (ARRAY, VARIANT, …)

PROXY_LEAN = {".string": "String", ".int": "Int", ".bool": "Bool", ".float": "Rat"}

def ident(name: str) -> str:
    s = re.sub(r"[^0-9a-zA-Z_]", "_", name)
    if s and s[0].isdigit(): s = "c_" + s
    if s in LEAN_KEYWORDS:   s = s + "_"
    return s

def parse_ddl(ddl: str):
    """Return {TABLE_NAME: [(colname, sqltype), ...]}."""
    tables = {}
    for m in re.finditer(r"(?:create or replace\s+)?TABLE\s+([^\s(]+)\s*\(([\s\S]*?)\)\s*;", ddl, re.I):
        name = m.group(1).split(".")[-1].strip('"').upper()
        cols = []
        for line in m.group(2).splitlines():
            line = line.strip().rstrip(",")
            if not line: continue
            cm = re.match(r'"?([0-9a-zA-Z_]+)"?\s+(.+)', line)
            if cm: cols.append((cm.group(1), cm.group(2).strip()))
        if cols: tables[name] = cols
    return tables

def referenced_tables(sqls, ddl_tables):
    """Tables (in DDL) that the SQL variants mention, in first-seen order."""
    seen = []
    joined = "\n".join(sqls)
    # qualified  "A"."B"."C"  -> C ;  also bare FROM/JOIN <name>
    cands = re.findall(r'"[^"]+"\."[^"]+"\."([^"]+)"', joined)
    cands += re.findall(r'(?:FROM|JOIN)\s+"?([0-9A-Za-z_]+)"?', joined, re.I)
    for c in cands:
        u = c.strip('"').upper()
        if u in ddl_tables and u not in seen:
            seen.append(u)
    return seen

def emit_schema(table, cols, prefix=""):
    """Emit the table schema in the parser's canonical form: a `List SQLTypeProxy`
    (so `colTypeOfList`/`sqlTypeDecEq` give the type + DecidableEq, exactly what
    LeanDatabase.Parser produces from the DDL) plus one named projection per column."""
    n = len(cols)
    proxies = ", ".join(sql_proxy(t) for _,t in cols)
    lines = [
        f"/-- Full `{table}` schema ({n} columns) in the parser's canonical form. -/",
        f"abbrev {table} : List SQLTypeProxy := [{proxies}]",
        "",
        f"-- column projections for {table}",
    ]
    for i,(c,t) in enumerate(cols):
        lt = PROXY_LEAN[sql_proxy(t)]
        lines.append(f"abbrev {prefix}{ident(c)} : TypedTupleOfList {table} → {lt} := fun t => t {i}")
    return "\n".join(lines)

def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    flags = [a for a in sys.argv[1:] if a.startswith("--")]
    if not args:
        sys.exit("usage: scaffold.py <instance_id> [--force] [--tables T1,T2]")
    iid = args[0]
    force = "--force" in flags
    tbl_override = next((f.split("=",1)[1] for f in flags if f.startswith("--tables")), None)

    recs = {json.loads(l)["instance_id"]: json.loads(l) for l in open(DATA)}
    if iid not in recs: sys.exit(f"instance {iid} not found")
    r = recs[iid]
    sqls = r["equivalent_sqls"]

    ddl_tables = parse_ddl(r.get("ddl",""))
    if tbl_override:
        tables = [t.strip().upper() for t in tbl_override.split(",")]
    else:
        tables = referenced_tables([s["sql"] for s in sqls], ddl_tables)
    if not tables:
        print("WARNING: no DDL tables detected; emitting no schema.", file=sys.stderr)

    mod = iid[0].upper() + iid[1:]
    out = os.path.join(HERE, f"{mod}.lean")
    if os.path.exists(out) and not force:
        sys.exit(f"{out} exists; pass --force to overwrite")

    # If >1 table, prefix projections with the table name to avoid column collisions.
    multi = len(tables) > 1

    P = []
    P.append("import LeanDatabase.SQLEquiv")
    P.append("import LeanDatabase.Parser")
    P.append("open LeanDatabase")
    P.append("")
    P.append("/-!")
    P.append(f"# Cross-skill instance `{iid}`")
    P.append("")
    P.append(f"**Question:** {r['natural_language_question']}")
    P.append("")
    P.append(f"Variants claimed equivalent: {len(sqls)}. Tables encoded (full schema): "
             + (", ".join(tables) if tables else "none"))
    P.append("")
    for s in sqls:
        P.append(f"## variant [{s['skill']}]")
        P.append("```sql")
        P.append(s["sql"].strip())
        P.append("```")
        P.append("")
    P.append("**Difference (winnable pair):** TODO — describe the pure-algebra difference.")
    P.append("-/")
    P.append("")
    P.append(f"namespace CrossSkill.{mod}")
    P.append("")
    for t in tables:
        P.append(emit_schema(t, ddl_tables[t], prefix=(t.lower()+"_" if multi else "")))
        P.append("")
    rel0 = tables[0] if tables else "SCHEMA"
    P.append("/- TODO: encode the two variants as query terms over the schema(s) above,")
    P.append("   then prove them equal. Replace the placeholder below. -/")
    P.append("")
    P.append(f"-- def q_a (R : TypedRelationOfList {rel0}) := ...")
    P.append(f"-- def q_b (R : TypedRelationOfList {rel0}) := ...")
    P.append("")
    P.append(f"-- theorem equiv (R : TypedRelationOfList {rel0}) : q_a R = q_b R := by")
    P.append("--   sql_equiv")
    P.append("")
    P.append(f"end CrossSkill.{mod}")

    with open(out, "w") as f:
        f.write("\n".join(P) + "\n")
    print(f"wrote {out}  (tables: {', '.join(tables) or 'none'})")

if __name__ == "__main__":
    main()
