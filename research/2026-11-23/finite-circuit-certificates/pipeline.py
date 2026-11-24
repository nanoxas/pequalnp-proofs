#!/usr/bin/env python3
"""Prepare a standalone Lean proof for an explicit posted five-input row.

This program never runs Lean, accesses the network, or changes a task lease.
It supports the positive finite-family one-NOT-removal statement used by the
project desk. The exact supplied statement is retained in the final theorem.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

import formula_upper
from live_checker import Evaluator, TOP, audit_raw, make_raw

HERE = Path(__file__).resolve().parent
BODY_SHA256 = "19a0ec27e0a5f2a6010436f261f4b74e7db8a4e454af7e6a253e5a691c5fd527"
SUPPORTED_BODY = """∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ),
(∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
g.inputs.length ≤ 2) →
(∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not →
(gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
(∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) =
Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) →
∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ),
(∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool,
PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) =
Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)"""


class PrerequisiteError(Exception):
    def __init__(self, code, message, index=None):
        super().__init__(message)
        self.code, self.message, self.index = code,message,index

    def record(self):
        return {"status":"FAILED_PREREQUISITE","code":self.code,"message":self.message,
                "index":self.index,"lean_source_generated":False,"kernel_check_status":"not_run"}


def need(condition, code, message, index=None):
    if not condition:
        raise PrerequisiteError(code,message,index)


def number(value, name="integer"):
    if type(value) is int:
        return value
    if isinstance(value,str) and re.fullmatch(r"(?:0[xX][0-9a-fA-F]+|[0-9]+)",value):
        return int(value,16 if value.lower().startswith("0x") else 10)
    raise PrerequisiteError("INVALID_INTEGER",f"{name} must be an unsigned integer or a hexadecimal string")


def compact(text):
    return re.sub(r"\s+"," ",text.strip())


def statement_for(tables):
    """Canonical supported sentence, useful for documentation and synthetic tests."""
    return "∀ T ∈ ({"+", ".join(hex(t) for t in tables)+"} : Finset ℕ), "+compact(SUPPORTED_BODY)


def parse_row(row):
    need(isinstance(row,dict),"INVALID_ROW","The public row must be a JSON object")
    need(not row.get("checked") and not row.get("withdrawn"),"CLOSED_ROW","The supplied public row is marked checked or withdrawn")
    ident = row.get("id","")
    need(isinstance(ident,str) and re.fullmatch(r"L-meta-[0-9]+",ident),"INVALID_ROW_ID","Expected a public L-meta-N row identifier")
    module = row.get("module",f"PEqualNP.Outside.L_meta_{ident.rsplit('-',1)[-1]}")
    expected_module = f"PEqualNP.Outside.L_meta_{ident.rsplit('-',1)[-1]}"
    need(module == expected_module,"UNSUPPORTED_MODULE","The row module must match its L-meta identifier")
    text = row.get("statement")
    need(isinstance(text,str),"MISSING_STATEMENT","The row must include its exact posted Lean statement")
    match = re.fullmatch(r"∀\s+T\s+∈\s+\(\{([^{}]*)\}\s*:\s*Finset\s+ℕ\),\s*(.*)",text.strip(),re.S)
    need(match is not None,"UNSUPPORTED_STATEMENT","Expected a finite family of five-input truth tables in the supported positive statement")
    need(compact(match[2]) == compact(SUPPORTED_BODY),"UNSUPPORTED_STATEMENT","The posted sentence differs from the supported five-input one-NOT-removal statement")
    pieces = match[1].split(',')
    need(all(p.strip() for p in pieces),"EMPTY_TABLE_FAMILY","The posted table family must be nonempty")
    tables = [number(p.strip(),"truth table") for p in pieces]
    need(len(set(tables)) == len(tables),"DUPLICATE_TABLE","The posted table family contains repeated values")
    need(all(0 <= t < 2**32 for t in tables),"TABLE_OUT_OF_RANGE","Every truth table must fit 32 bits")
    imports = row.get("imports",["PEqualNP.Defs"])
    need(isinstance(imports,list) and "PEqualNP.Defs" in imports,"MISSING_DEFS_IMPORT","The row must permit PEqualNP.Defs")
    return {"id":ident,"module":module,"statement":text,"tables":tables}


def load_json(path):
    try:
        return json.loads(Path(path).read_text())
    except (OSError,json.JSONDecodeError) as exc:
        raise PrerequisiteError("INVALID_JSON",f"Could not read JSON from {Path(path).name}: {type(exc).__name__}") from exc


def reject_incomplete_claims(value, index):
    if isinstance(value,list):
        for item in value:
            reject_incomplete_claims(item,index)
    elif isinstance(value,dict):
        if "status" in value:
            need(value["status"] == "COMPLETE","UNKNOWN_SEARCH_STATUS","A supplied search record is not COMPLETE; regenerate it explicitly",index)
            if "result" in value:
                need(value["result"] is False,"SEARCH_RETURNED_TRUE","A supplied rejection search returned true",index)
        for item in value.values():
            reject_incomplete_claims(item,index)


def normalize_records(row, data):
    records = data.get("tables") if isinstance(data,dict) else data
    need(isinstance(records,list),"INVALID_CERTIFICATES","Certificate JSON must be a list or contain a tables list")
    need(len(records) == len(row["tables"]),"MISSING_TABLE_RECORD","Exactly one record is required for each posted truth table")
    result = []
    seen = set()
    for default_index,record in enumerate(records):
        need(isinstance(record,dict),"INVALID_RECORD","Each certificate record must be an object",default_index)
        i = number(record.get("index",default_index),"table index")
        need(0 <= i < len(row["tables"]) and i not in seen,"BAD_TABLE_INDEX","Table indices must be distinct and cover the posted family",i)
        seen.add(i)
        table = number(record.get("truth_table"),"truth table")
        need(table == row["tables"][i],"TABLE_ORDER_MISMATCH","The record does not match its posted truth table",i)
        need(formula_upper.monotone(table),"NONMONOTONE_TABLE","The supported row requires a monotone truth table",i)
        essential = formula_upper.essential_variables(table)
        need(all(essential),"NONESSENTIAL_VARIABLES",f"The accepted cost interface requires five essential variables; flags are {essential}",i)
        gates = record.get("gates")
        output = record.get("output")
        need(isinstance(gates,list),"INVALID_WITNESS","A monotone witness gate list is required",i)
        normalized_gates = []
        for j,g in enumerate(gates):
            need(isinstance(g,dict) and isinstance(g.get("inputs"),list),"INVALID_WITNESS",f"Gate {j} must contain op and inputs",i)
            op = g.get("op")
            need(op in ("and","or"),"NONMONOTONE_WITNESS",f"Gate {j} must use and or or",i)
            normalized_gates.append({"op":op,"inputs":[number(a,"wire") for a in g["inputs"]]})
        witness = {"gates":normalized_gates,"output":number(output,"output wire")}
        try:
            witness_table = formula_upper.evaluate(witness)
        except ValueError as exc:
            raise PrerequisiteError("INVALID_WITNESS",str(exc),i) from exc
        need(witness_table == table,"WRONG_WITNESS_TABLE","The monotone witness fails the full 32-row truth table",i)
        need(len(gates) > 0,"EMPTY_WITNESS","The five-essential-variable interface needs a nonempty witness",i)
        lower_s = number(record.get("lower_s",len(gates)-1),"rejection bound")
        need(lower_s+1 == len(gates),"WRONG_REJECTION_BOUND","The rejection bound must be exactly witness size minus one",i)
        raw_data = record.get("raw")
        if raw_data is None:
            raw = make_raw(table)
        else:
            need(isinstance(raw_data,list) and len(raw_data)==5,"INVALID_RAW_LENGTH","Raw signatures must contain exactly five pairs",i)
            need(all(isinstance(a,list) and len(a)==2 for a in raw_data),"INVALID_RAW_PAIR","Each raw signature must contain two integers",i)
            raw = tuple((number(a,"positive bits"),number(b,"negative bits")) for a,b in raw_data)
            need(all(0<=a<=TOP and 0<=b<=TOP for a,b in raw),"RAW_OUT_OF_RANGE","Each sample vector must fit 256 bits",i)
        raw_audit = audit_raw(table,raw)
        need(raw_audit["samples_correct"],"BAD_SAMPLE_LABEL","At least one sample column has the wrong truth-table label",i)
        need(raw_audit["nodup"],"DUPLICATE_RAW_SIGNATURE","The five raw input signatures must be distinct",i)
        need(all(raw_audit["essential_inputs"]),"NONESSENTIAL_SAMPLED_VARIABLE","The supplied samples do not certify all five variables as essential",i)
        for key in ("search_results","searches"):
            if key in record:
                reject_incomplete_claims(record[key],i)
        if "search_status" in record:
            need(record["search_status"] == "COMPLETE","UNKNOWN_SEARCH_STATUS","A supplied search status is not COMPLETE",i)
        result.append({"index":i,"truth_table":hex(table),"lower_s":lower_s,
                       "raw":[[hex(a),hex(b)] for a,b in raw],**witness,
                       "input_audit":raw_audit,"witness_verified_rows":32})
    return sorted(result,key=lambda r:r["index"])


def audit_records(records, seconds=120, cache_size=100_000, max_states=2_000_000, progress=None):
    results = []
    for record in records:
        i = record["index"]
        raw = tuple((int(a,16),int(b,16)) for a,b in record["raw"])
        searches = []
        for t in (0,1):
            answers = []
            for reference in (False,True):
                answer = Evaluator(reference=reference,seconds=seconds,cache_size=cache_size,max_states=max_states).run(record["lower_s"],t,raw)
                need(answer["status"] == "COMPLETE","UNKNOWN_SEARCH_STATUS",f"Search at NOT count {t} is UNKNOWN: {answer.get('reason','unspecified')}",i)
                need(answer["result"] is False,"SEARCH_RETURNED_TRUE",f"Search at NOT count {t} returned true; this data does not certify the proposed lower bound",i)
                answers.append(answer)
            need(answers[0]["unrolled_search_calls"] == answers[1]["unrolled_search_calls"],"EVALUATOR_DISAGREEMENT","Optimized and reference evaluators differ in recursive work",i)
            searches.append({"not_count":t,"optimized":answers[0],"reference":answers[1]})
        results.append({"index":i,"truth_table":record["truth_table"],"lower_s":record["lower_s"],"searches":searches})
        if progress:
            progress(results)
    return results


def generic_engine():
    body = (HERE/"engine/GenericBody.lean.inc").read_text()
    need(hashlib.sha256(body.encode()).hexdigest() == BODY_SHA256,"ENGINE_BODY_CHANGED","The accepted generic body no longer matches its pinned hash")
    imports = (HERE/"engine/imports.txt").read_text()
    expected = ["Mathlib.Data.Finset.Card","Mathlib.Data.Finset.Dedup","Mathlib.Tactic.ByContra",
                "Mathlib.Tactic.FinCases","Mathlib.Tactic.Ext","PEqualNP.Defs"]
    need(imports.splitlines() == ["import "+s for s in expected],"IMPORT_HEADER_CHANGED","The agreed six-import header has changed")
    return body,imports


def gate_literal(gate):
    return "⟨."+gate["op"]+", ["+", ".join(str(a) for a in gate["inputs"])+"]⟩"


def table_source(record):
    i,T,s = record["index"],int(record["truth_table"],16),record["lower_s"]
    pairs = ",\n  ".join(f"(0x{int(a,16):064x}, 0x{int(b,16):064x})" for a,b in record["raw"])
    gates = "["+", ".join(gate_literal(g) for g in record["gates"])+"]"
    return f"""def raw_{i} : List Sig := [
  {pairs}]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rejected_{i}_zero : search {s} 0 raw_{i} = false := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rejected_{i}_one : search {s} 1 raw_{i} = false := by
  decide +kernel

lemma upper_{i} :
    ∃ (gs : List Gate) (o : ℕ),
      (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs.length = {s+1} ∧ ∀ x : Fin 5 → Bool,
      Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT {T} x := by
  refine ⟨{gates}, {record['output']}, ?_, rfl, ?_⟩
  · simp
  · decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table_{i} (gs : List Gate) (o : ℕ)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧
      g.inputs.length ≤ 2)
    (single : ∀ i j : Fin gs.length, (gs.get i).op = .not →
      (gs.get j).op = .not → i = j)
    (correct : ∀ x : Fin 5 → Bool,
      Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT {T} x) :
    ∃ (gs' : List Gate) (o' : ℕ),
      (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool,
      Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT {T} x := by
  have hlegal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff,
      Set.mem_singleton_iff] using legal
  have bound := cost {T} raw_{i} {s}
    rfl (by decide +kernel) (by decide +kernel) rfl (by decide +kernel)
    (by
      intro t
      fin_cases t
      · exact rejected_{i}_zero
      · exact rejected_{i}_one) ⟨gs,o⟩ hlegal single correct
  obtain ⟨gs',o',hops,hlen,heval⟩ := upper_{i}
  refine ⟨gs',o',hops,?_,heval⟩
  rw [hlen]
  exact Nat.succ_le_of_lt bound
"""


def lean_source(row, records):
    body,imports = generic_engine()
    namespace = row["module"]+"_aux"
    branches = "\n".join(f"  · exact {namespace}.table_{r['index']} gs o legal single correct" for r in records)
    cases = " | ".join("rfl" for _ in records)
    principal = f"""theorem {row['module']} : {row['statement']} := by
  intro T hT gs o legal single correct
  simp only [Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with {cases}
{branches}
"""
    return (imports+"\n-- The live-wire semantics and search are adapted from L-meta-1007, Apache-2.0.\n"
            "-- The unchanged generic core is reused from the checked L-meta-1445 contribution, Apache-2.0.\n"
            "-- Generated source: the minimized import header and this full file still require Lean checking.\n"
            f"namespace {namespace}\n"+body+"\nopen PEqualNP.CircuitLowerBounds\n\n"+
            "\n".join(table_source(r) for r in records)+f"\nend {namespace}\n\n"+principal)


def write_json(path, data):
    Path(path).write_text(json.dumps(data,indent=2)+"\n")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command",required=True)
    upper = sub.add_parser("witnesses",help="Generate monotone upper witnesses for the explicit row")
    upper.add_argument("--row",type=Path,required=True)
    upper.add_argument("--output",type=Path,required=True)
    upper.add_argument("--max-formula-cost",type=int,default=16)
    upper.add_argument("--seconds",type=float,default=60)
    for command in ("audit","build"):
        p = sub.add_parser(command,help="Audit all prerequisites" if command=="audit" else "Audit and emit standalone Lean source")
        p.add_argument("--row",type=Path,required=True)
        p.add_argument("--certificates",type=Path,required=True)
        p.add_argument("--out",type=Path,required=True)
        p.add_argument("--seconds",type=float,default=120,help="Time budget for each evaluator and NOT count")
        p.add_argument("--cache-size",type=int,default=100_000)
        p.add_argument("--max-states",type=int,default=2_000_000)
    args = parser.parse_args(argv)
    try:
        need(args.seconds >= 0,"INVALID_LIMIT","Time limit must be nonnegative")
        row = parse_row(load_json(args.row))
        if args.command == "witnesses":
            need(args.max_formula_cost >= 0,"INVALID_LIMIT","Formula cost limit must be nonnegative")
            for i,table in enumerate(row["tables"]):
                need(formula_upper.monotone(table),"NONMONOTONE_TABLE","The posted table is not monotone",i)
                need(all(formula_upper.essential_variables(table)),"NONESSENTIAL_VARIABLES","The current certificate engine requires five essential variables",i)
            result = formula_upper.generate(row["tables"],args.max_formula_cost,args.seconds)
            for i,record in enumerate(result["tables"]):
                record.update({"index":i,"lower_s":len(record["gates"])-1})
            args.output.parent.mkdir(parents=True,exist_ok=True)
            write_json(args.output,result)
            print(json.dumps({"status":"UPPER_WITNESSES_ONLY","output":str(args.output),
                              "sizes":[len(r["gates"]) for r in result["tables"]]}))
            return 0
        need(args.cache_size >= 0 and args.max_states >= 0,"INVALID_LIMIT","Search resource limits must be nonnegative")
        args.out.mkdir(parents=True,exist_ok=True)
        source_path = args.out/(row["module"].rsplit('.',1)[1]+".lean")
        need(not source_path.exists(),"OUTPUT_EXISTS","The output directory already contains a source file for this row; choose a fresh directory")
        records = normalize_records(row,load_json(args.certificates))
        def progress(results):
            write_json(args.out/"audit-progress.json",{"status":"IN_PROGRESS","completed_tables":results,"kernel_check_status":"not_run"})
        searches = audit_records(records,args.seconds,args.cache_size,args.max_states,progress)
        write_json(args.out/"certificates.json",records)
        write_json(args.out/"audit.json",{"status":"PYTHON_AUDIT_PASS","searches":searches,"kernel_check_status":"not_run"})
        manifest = {"task":row["id"],"module":row["module"],"status":"PYTHON_AUDIT_PASS",
                    "kernel_check_status":"not_run","eligibility":"Caller must independently verify current public status and authorized task scope.",
                    "minimal_header_status":"Not yet Lean-checked in this environment.",
                    "row_sha256":hashlib.sha256(args.row.read_bytes()).hexdigest(),
                    "certificate_input_sha256":hashlib.sha256(args.certificates.read_bytes()).hexdigest(),
                    "engine_body_sha256":BODY_SHA256,"tables":len(records),
                    "searches":2*len(records),"reference_agreements":2*len(records)}
        if args.command == "build":
            source = lean_source(row,records)
            source_path.write_text(source)
            manifest.update({"status":"GENERATED_UNCHECKED","source":source_path.name,
                             "source_sha256":hashlib.sha256(source.encode()).hexdigest(),"source_bytes":len(source.encode())})
        write_json(args.out/"manifest.json",manifest)
        write_json(args.out/"audit-progress.json",{"status":"COMPLETE","kernel_check_status":"not_run","completed_tables":len(records)})
        print(json.dumps(manifest,indent=2))
        return 0
    except PrerequisiteError as exc:
        error = exc.record()
        if hasattr(args,"out"):
            args.out.mkdir(parents=True,exist_ok=True)
            write_json(args.out/"failed-status.json",error)
        print(json.dumps(error,indent=2),file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
