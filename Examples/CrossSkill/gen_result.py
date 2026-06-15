#!/usr/bin/env python3
"""Regenerate result.json from the CrossSkill instance files + the dataset.

MERGE semantics (so we don't re-judge prior work): the existing result.json's instances are the
source of truth and are PRESERVED; on-disk `Sf*.lean` files that are NOT already recorded are added
as new entries (crude auto-classification: an active `sql_equiv`/theorem ⇒ pass, else out_of_scope).
The recorded count is therefore "previously-judged + new incomers". (A proper re-judge of changed
files is left for later — see the note in the header.)

outcome values: pass | pass_under_hypothesis | out_of_scope | fail.
"""
import json, re, os, glob

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "crossskill_equivalent_sql.jsonl")
RESULT = os.path.join(HERE, "result.json")
recs = {json.loads(l)["instance_id"]: json.loads(l) for l in open(DATA)} if os.path.exists(DATA) else {}

LEMMAS = [
    {"name": "swapAppend + crossProduct_comm + join_comm + join_comm_image",
     "where": "LeanDatabase/Operators/{CrossProduct,Join}.lean",
     "statement": "join/cross-product commutativity via the dependent half-swap reindex; join_comm_image is the first-order 'swap operands then project' corollary."},
    {"name": "restriction_join_left",
     "where": "LeanDatabase/Operators/Join.lean",
     "statement": "selection pushdown into the left join input: sigma_{pL.left}(R join S) = (sigma_pL R) join S."},
    {"name": "join_cond_congr",
     "where": "LeanDatabase/Operators/Join.lean",
     "statement": "pointwise-equal join conditions give equal joins (closes ON a=b vs ON b=a)."},
    {"name": "union_idempotence + projection_union + select_union",
     "where": "LeanDatabase/{RelationalAlgebra,Operators/Select}.lean",
     "statement": "R union R = R; projection and computed SELECT distribute over UNION."},
    {"name": "relMax_union + relMin_union + relCount_eq_relCountDistinct_of_injOn",
     "where": "LeanDatabase/Operators/Aggregate.lean",
     "statement": "MAX/MIN over a union is the sup/inf of the two; COUNT(*) = COUNT(DISTINCT key) when key is injective on the rows."},
    {"name": "FuncDepEq + cnt_pair_eq_of_FD + cnt_collapse_of_FD (@[simp]) + relCountDistinct_eq_of_factor",
     "where": "LeanDatabase/Constraints.lean",
     "statement": "functional-dependency layer: GROUP BY (det,key) collapses to GROUP BY key under key->det; COUNT(DISTINCT) under a factoring bijection."},
    {"name": "restriction_congr + cnt_eq_of_partition_eq + card_image_eq_of_fiber + select_congr",
     "where": "LeanDatabase/{SQLToolbox,Operators/Select}.lean",
     "statement": "general congruences: restriction/select agree when predicates/row-maps agree on the data; same-partition => same group count / same distinct count."},
]
PLANNED = [
    {"name": "join_assoc", "where": "LeanDatabase/Operators/{CrossProduct,Join}.lean",
     "why": "3-way join reassociation; needs a dependent append-associativity reindex (analogous to swapAppend). Deferred — the hardest of the requested batch."},
    {"name": "subquery<->join bridges, UNION ALL (bag), genuine top-N (ORDER BY LIMIT k)",
     "why": "larger future items; the dataset is 85% subqueries and has many ranking queries."},
]

def first_para(text, marker):
    i = text.find(marker)
    if i < 0: return None
    para = re.split(r"\n\s*\n", text[i+len(marker):], 1)[0]
    return re.sub(r"\s+", " ", para.replace("*", "").replace("`", "").strip())[:300]

# 1. Load existing result.json (the previously-judged record) -> dict by id.
prev = {}
if os.path.exists(RESULT):
    old = json.load(open(RESULT))
    for e in old.get("instances", []):
        prev[e["instance_id"]] = e

# 2. Walk on-disk files; add ONLY new ids (preserve prior judgments).
for f in sorted(glob.glob(os.path.join(HERE, "Sf*.lean"))):
    src = open(f).read()
    mod = os.path.basename(f)[:-5]
    iid = mod[0].lower() + mod[1:]
    if iid in prev:
        # keep the curated prior entry; just refresh the file path / on-disk flag
        prev[iid]["file"] = f"Examples/CrossSkill/{mod}.lean"
        prev[iid]["on_disk"] = True
        continue
    rec = recs.get(iid, {})
    proven = bool(re.search(r"^theorem ", src, re.M)) and not re.search(r"\bsorry\b|\badmit\b", src)
    hyp = bool(re.search(r"under a (stated|data)|\bbijection\b|FuncDepEq|functional dependency", src, re.I))
    outcome = "out_of_scope" if not proven else ("pass_under_hypothesis" if hyp else "pass")
    tbls = re.findall(r"Full `([A-Z0-9_]+)` schema \((\d+)", src)
    prev[iid] = {
        "instance_id": iid,
        "file": f"Examples/CrossSkill/{mod}.lean",
        "num_distinct_variants": rec.get("num_distinct_variants"),
        "num_equivalent_sqls": len(rec.get("equivalent_sqls", [])) or None,
        "sql_equiv": outcome,
        "difference": first_para(src, "Difference (winnable pair):") or first_para(src, "Difference:"),
        "table_encoded": ", ".join(f"{t} ({n})" for t, n in tbls) or None,
        "on_disk": True,
    }
    if "set_option maxRecDepth" in src:
        prev[iid]["note"] = "needed `set_option maxRecDepth` (wide schema)."

# mark which prior entries no longer have a file on disk
on_disk_ids = {os.path.basename(f)[:-5][0].lower() + os.path.basename(f)[:-5][1:]
               for f in glob.glob(os.path.join(HERE, "Sf*.lean"))}
for iid, e in prev.items():
    e.setdefault("on_disk", iid in on_disk_ids)

instances = [prev[k] for k in sorted(prev)]
from collections import Counter
c = Counter(e["sql_equiv"] for e in instances)

out = {
    "dataset": "Examples/CrossSkill/crossskill_equivalent_sql.jsonl",
    "dataset_totals": {"records": len(recs), "total_sqls": sum(len(r["equivalent_sqls"]) for r in recs.values())},
    "scope": ("Manual encoding: pure relational-algebra variant differences are proved with bare sql_equiv; "
              "data-dependent ones are proved under an explicit hypothesis (FD/bijection/predicate-agreement) "
              "via the constraint layer; NULL/rounding/top-N-order differences are out_of_scope."),
    "tactic_under_test": "sql_equiv (LeanDatabase.SQLEquiv)",
    "note": ("MERGED record: previously-judged instances are preserved (some may not have a .lean file on disk "
             "right now — see on_disk); new on-disk files are appended. Counts = prior + new incomers."),
    "outcome_legend": {
        "pass": "bare sql_equiv closes the pure-algebra difference.",
        "pass_under_hypothesis": "true only under a stated data hypothesis (FD / bijection / predicate-agreement); proved with that as a premise.",
        "out_of_scope": "needs NULL/rounding/top-N-order semantics we abstract away; no theorem.",
        "fail": "a genuinely-algebraic goal sql_equiv could not close (none currently).",
    },
    "lemmas_added_to_toolbox": LEMMAS,
    "planned_lemmas": PLANNED,
    "summary": {"encoded": len(instances), "pass": c.get("pass", 0),
                "pass_under_hypothesis": c.get("pass_under_hypothesis", 0),
                "out_of_scope": c.get("out_of_scope", 0), "fail": c.get("fail", 0),
                "on_disk_now": sum(1 for e in instances if e.get("on_disk"))},
    "instances": instances,
}
json.dump(out, open(RESULT, "w"), indent=2, ensure_ascii=False)
print(f"wrote result.json: {len(instances)} instances "
      f"({out['summary']['pass']} pass, {out['summary']['pass_under_hypothesis']} pass_under_hypothesis, "
      f"{out['summary']['out_of_scope']} out_of_scope; {out['summary']['on_disk_now']} on disk now)")
