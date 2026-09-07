#!/usr/bin/env python3
"""Kernel-check the fourteen IMQ files and audit EVERY new Lean declaration.

The separate helper imports Lean.Elab.Print; the mathematical files stay
import-free. Environment differences include private/generated declarations and
names outside the advertised namespaces. Source theorem names are an independent
coverage/count check, never the enumeration used for the axiom audit.

Usage: python3 scripts/lean_audit.py [--keep-output [DIR]]
LEAN_AUDIT_OUTPUT_DIR also retains artifacts. --through labels a partial check;
only the default checks the complete fourteen-file release.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

PACKAGE = Path(__file__).resolve().parents[1]
TARGETS = (
    ("ImaginaryQuadraticDatum", "IMQ"), ("ModSevenImage", "IMQ7"),
    ("GeometricInput", "IMQGeom"), ("GeometricFinite", "IMQGeomFinite"),
    ("SplitReduction", "IMQSplit"), ("GeometricCompletion", "IMQGeomEF"),
    ("GeometricModels", "IMQGeomModels"),
    ("EntranceMargin", "IMQEntrance"), ("DeepImaginaryDatum", "IMQDeep"),
    ("BlurExceedsMargin", "BlurMargin"),
    ("LargeImaginaryDatum", "IMQLarge"),
    # ADDED 2026-09-07 (final check).  These two were shipped but not audited; in
    # particular BasisFreeImage carries the basis-free image argument that the paper
    # cites as closing the most serious review finding, so "every declaration" was
    # false of the shipped command.  All fourteen files are now in scope.
    ("RegardedUpToIsOrbit", "RegardedUpTo"),
    ("BasisFreeImage", "BasisFree"),
    # ADDED 2026-09-07.  The finite arithmetic behind Proposition 2 -- specifically the
    # exclusion of q = p that external review found missing from the sieve's root count.
    ("FamilyArithmetic", "FamilyArith"),
)
# Names in the original 27 + 33 + 14 theorem baseline. This checks preservation
# of the declarations, not semantic identity of all their source text.
BASELINE = {
    "ImaginaryQuadraticDatum": """p_prime p_split norm_pi pi_pib orbit1 orbit2
      orbit3 orbit4 orbit5 orbit6 j_not_rational a_is_pi_pow pi_not_dvd_pib
      pib_not_dvd_a pi_not_dvd_oma pib_not_dvd_oma norm_a norm_oma_factored
      seven_not_dvd_norm_oma sieve_bound_is_seventh_root ord_q
      seven_not_dvd_ord_q seven_not_dvd_small eb_val gcd_ord_eb tame ord_qbb""".split(),
    "ModSevenImage": """root13 root17 root37 root41 root53 root61 tr13 tr17
      tr37 tr41 tr53 tr61 nonsq13 nonsq17 nonsq37 nonsq41 nonsq53 nonsq61
      other_place_13_fails other_place_61_fails compInv13 compInv17 compInv37
      compInv41 compInv53 compInv61 gen13 gen17 gen37 gen41 gen53 gen61
      index_prime_to_seven""".split(),
    "GeometricInput": """jDen_ne_zero j_not_rational exc_all_rational sl7_card
      flags_card flags_transitive stabiliser_order two_xi_ne_pm_xi
      core_of_irrational_j core_of_datum witness_arithmetic_inhabited
      witness_core_fails witness_core_holds mfhmp_is_necessary""".split(),
}
ALLOWED_AXIOMS = {"propext", "Quot.sound"}
BASELINE_SHA256 = {
    "ImaginaryQuadraticDatum": "e033877320cb8b1af2b4f7cfbcb4b816b5982a59c5fd20d6f4013f2a7dab8940",
    "ModSevenImage": "7c6a4c5cb711429bf9bdeeaaf136647bd1de1626eac1d3d08924308ecf83d2bf",
    "GeometricInput": "6c0df6721a4db238e96a5ad6eb56cbe7180b9c97bb5682940f893eb08194f128",
}


# Preserve the previous 140-theorem / 481-declaration release as well as the
# original 74-theorem baseline. New files cannot replace or mask old sources.
GEOMETRY_BASELINE_SHA256 = {
    **BASELINE_SHA256,
    "GeometricFinite": "994f22e1122d124b251e220f62ef3fdf632cbd22c16a452d0e568d9790d33024",
    "SplitReduction": "d6f6f40f8d6a25272ed50074690dad5a3594254030cf079a83a4a0fb58eadb7e",
    "GeometricCompletion": "d6cff07cadd358d80acf21d7d4b7f7140727f4bddc9913a060734428a99efe19",
    "GeometricModels": "47e25e7e5c2d5890c733b8d08a717f558c2208ebf2192803a98e542d76094f9f",
}

# An initialize declaration cannot be evaluated from its own module; compile
# this helper separately. No helper declarations count as mathematical input.
HELPER = r'''import Lean.Elab.Print
open Lean Elab Command
initialize leanAuditBaseline : IO.Ref (Std.HashSet Name) ← IO.mkRef {}
elab "#lean_audit_begin" : command => do
  let env ← getEnv
  let names := env.constants.fold (init := ({} : Std.HashSet Name)) fun acc n _ => acc.insert n
  liftIO <| leanAuditBaseline.set names
elab "#lean_audit_end " label:str : command => do
  let env ← getEnv
  let baseline ← liftIO <| leanAuditBaseline.get
  let names := env.constants.fold (init := (#[] : Array Name)) fun acc n _ =>
    if baseline.contains n then acc else acc.push n
  let file := label.getString
  for n in names.qsort Name.lt do
    let c := env.constants.find! n
    let kind := match c with
      | .axiomInfo _ => "axiom"
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    let userName := privateToUserName n
    logInfo m!"LEAN_AUDIT_DECL|{file}|{n}|{userName}|{kind}"
    elabCommand (← `(#print axioms $(mkIdent n)))
    let axioms ← collectAxioms n
    let deps := String.intercalate "," (axioms.qsort Name.lt |>.toList.map Name.toString)
    logInfo m!"LEAN_AUDIT_DEPS|{file}|{n}|{deps}"
  logInfo m!"LEAN_AUDIT_TOTAL|{file}|{names.size}"
'''

class AuditError(Exception):
    pass

def strip_noncode(text: str) -> str:
    """Blank nested comments/strings but preserve offsets. Enumeration uses Lean,
    not this small lexer; it serves only the supplementary source checks."""
    chars = list(text)
    i = 0
    while i < len(text):
        start = i
        if text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end == -1 else end
        elif text.startswith("/-", i):
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise AuditError("unterminated Lean comment")
        elif text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            if i >= len(text):
                raise AuditError("unterminated Lean string")
            i += 1
        else:
            i += 1
            continue
        for j in range(start, min(i, len(chars))):
            if chars[j] != "\n":
                chars[j] = " "
    return "".join(chars)

IDENT = r"[A-Za-z_\u0080-\uffff][A-Za-z_0-9'\u0080-\uffff]*(?:\.[A-Za-z_\u0080-\uffff][A-Za-z_0-9'\u0080-\uffff]*)*"
COMMAND = re.compile(
    rf"(?m)^[ \t]*(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    rf"(?P<kind>namespace|section|end|theorem|lemma)\b(?:[ \t]+(?P<name>{IDENT}))?"
)

def authored_theorems(code: str, file: str) -> list[str]:
    """Inventory ordinary named theorem commands; unsupported syntax fails closed.
    Generated kernel theorem declarations are counted separately."""
    stack: list[tuple[str, str]] = []
    names = []
    occurrences = 0
    for match in COMMAND.finditer(code):
        kind, name = match["kind"], match["name"]
        if kind in ("namespace", "section"):
            stack.append((kind, name or ""))
        elif kind == "end":
            if not stack:
                raise AuditError(f"{file}: unmatched end in source inventory")
            stack.pop()
        else:
            occurrences += 1
            if not name:
                raise AuditError(f"{file}: unnamed/unsupported theorem command")
            namespace = ".".join(n for k, n in stack if k == "namespace")
            names.append(name.removeprefix("_root_.") if name.startswith("_root_.")
                         else ".".join(filter(None, (namespace, name))))
    if stack:
        raise AuditError(f"{file}: unclosed namespace/section in source inventory")
    tokens = len(re.findall(r"\b(?:theorem|lemma)\b", code))
    if tokens != occurrences or len(set(names)) != len(names):
        raise AuditError(f"{file}: unenumerated/duplicate authored theorem syntax")
    if not names:
        raise AuditError(f"{file}: zero authored theorems")
    return names

def parse_audit_output(output: str, expected: dict[str, list[str]]) -> dict:
    """Require marker + one standard print report + dependencies for every name."""
    errors: list[str] = []
    decls: dict[tuple[str, str], dict] = {}
    totals: dict[str, int] = {}
    active = None
    for line in output.splitlines():
        if line.startswith("LEAN_AUDIT_DECL|"):
            parts = line.split("|")
            if len(parts) != 5:
                errors.append("malformed declaration marker")
                continue
            _, file, name, user_name, kind = parts
            key = (file, name)
            if active is not None or key in decls:
                errors.append(f"duplicate/incomplete declaration report: {key}")
            decls[key] = {"file": file, "name": name, "user_name": user_name,
                          "kind": kind, "print_reports": 0, "axioms": None}
            active = key
        elif line.startswith("LEAN_AUDIT_DEPS|"):
            parts = line.split("|")
            if len(parts) != 4:
                errors.append("malformed dependency marker")
                continue
            _, file, name, deps = parts
            key = (file, name)
            if active != key or key not in decls:
                errors.append(f"unmatched dependency row: {key}")
            else:
                decls[key]["axioms"] = deps.split(",") if deps else []
            active = None
        elif line.startswith("LEAN_AUDIT_TOTAL|"):
            parts = line.split("|")
            if len(parts) != 3 or not parts[2].isdigit():
                errors.append("malformed total marker")
                continue
            _, file, count = parts
            if file in totals:
                errors.append(f"duplicate file total: {file}")
            totals[file] = int(count)
        elif "does not depend on any axioms" in line or "depends on axioms:" in line:
            if active not in decls:
                errors.append("axiom print report outside a declaration block")
            else:
                decls[active]["print_reports"] += 1
    if active is not None:
        errors.append("unterminated declaration report")
    if not decls:
        errors.append("zero declaration output")
    if set(totals) != set(expected):
        errors.append("missing/unexpected file totals")
    per_file = {}
    for file, authored in expected.items():
        rows = [d for d in decls.values() if d["file"] == file]
        if not rows or totals.get(file) != len(rows):
            errors.append(f"{file}: zero output or declaration/total mismatch")
        found = Counter(d["user_name"] for d in rows if d["kind"] == "theorem")
        for theorem in authored:
            if found[theorem] != 1:
                errors.append(f"{file}: missing/duplicate authored theorem: {theorem}")
        authored_rows = [d for d in rows if d["kind"] == "theorem" and d["user_name"] in authored]
        per_file[file] = {
            "authored_theorems": len(authored), "declarations": len(rows),
            "kernel_theorems": sum(d["kind"] == "theorem" for d in rows),
            "authored_axiom_free": sum(d["axioms"] == [] for d in authored_rows),
            "authored_with_axioms": sum(bool(d["axioms"]) for d in authored_rows),
        }
    for d in decls.values():
        if d["file"] not in expected:
            errors.append(f"unexpected file declaration: {d['file']}")
        if d["print_reports"] != 1 or d["axioms"] is None:
            errors.append(f"missing/duplicate axiom report: {d['name']}")
        if d["kind"] == "axiom":
            errors.append(f"new custom axiom declaration: {d['name']}")
        forbidden = set(d["axioms"] or []) - ALLOWED_AXIOMS
        if forbidden:
            errors.append(f"forbidden axiom dependency: {d['name']}: {', '.join(sorted(forbidden))}")
    return {
        "errors": errors, "files": per_file, "declarations": list(decls.values()),
        "total_declarations": len(decls),
        "total_authored_theorems": sum(len(v) for v in expected.values()),
        "axiom_free_declarations": sum(d["axioms"] == [] for d in decls.values()),
        "with_axiom_declarations": sum(bool(d["axioms"]) for d in decls.values()),
        "axiom_sets": dict(Counter(", ".join(d["axioms"] or []) or "(none)" for d in decls.values())),
    }

def run_command(command: list[str], cwd: Path, env: dict, log: Path, timeout: int) -> int:
    with log.open("w") as stream:
        try:
            return subprocess.run(command, cwd=cwd, env=env, stdout=stream,
                stderr=subprocess.STDOUT, timeout=timeout, check=False).returncode
        except subprocess.TimeoutExpired:
            stream.write(f"\nFAIL: timeout after {timeout} seconds\n")
            return 124

def audit(args: argparse.Namespace, work: Path) -> dict:
    targets = list(TARGETS)
    if args.through:
        targets = targets[:1 + [f for f, _ in targets].index(args.through)]
    expected, manifest, source_texts = {}, [], []
    source_holes = []
    for file, namespace in targets:
        source = args.source_dir / f"{file}.lean"
        if not source.is_file():
            raise AuditError(f"required source is missing: {source}")
        raw = source.read_bytes()
        text = raw.decode("utf-8")
        code = strip_noncode(text)
        # Anonymous examples are not persistent environment declarations.  Run
        # Lean first (so named-theorem mutation tests still witness sorryAx),
        # then reject holes anywhere in source, including these examples.
        for hole in re.finditer(r"\b(?:sorry|admit)\b", code):
            source_holes.append({"file": file, "line": code.count("\n", 0, hole.start()) + 1,
                                 "token": hole.group()})
        if re.search(r"\bnative_decide\b", code):
            raise AuditError(f"{file}: native_decide is forbidden")
        # A leading `import Init` is a no-op: Init is Lean's implicit prelude and
        # LeanAuditSupport already imports it.  It is the one import that may be
        # dropped without changing what the file means, so it is stripped from the
        # concatenated bundle (the file on disk is untouched; the manifest sha256
        # still covers the shipped bytes).  Every other import/prelude is rejected.
        text, n_init = re.subn(r"(?m)\A\s*import\s+Init[ \t]*\r?\n", "", text, count=1)
        code = strip_noncode(text)
        if re.search(r"(?m)^\s*(?:import|prelude)\b", code):
            raise AuditError(f"{file}: unexpected import/prelude in concatenated source")
        if "lean_audit" in code:
            raise AuditError(f"{file}: reserved audit command/name in source")
        names = authored_theorems(code, file)
        if not all(n.startswith(namespace + ".") for n in names):
            raise AuditError(f"{file}: authored theorem outside namespace {namespace}")
        baseline = {namespace + "." + n for n in BASELINE.get(file, [])}
        if baseline - set(names):
            raise AuditError(f"{file}: original theorem missing: {sorted(baseline - set(names))}")
        expected[file] = names
        # Exact input snapshot: concurrent edits cannot silently alter this run.
        (work / source.name).write_bytes(raw)
        manifest.append({"source": str(source.resolve()), "file": file,
                         "namespace": namespace, "sha256": hashlib.sha256(raw).hexdigest(),
                         "authored_theorems": names})
        source_texts.append((file, text))
    (work / "input-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    (work / "LeanAuditSupport.lean").write_text(HELPER)
    wrapper = "import LeanAuditSupport\nset_option Elab.async false\n"
    for file, text in source_texts:
        wrapper += "\n#lean_audit_begin\n" + text + f'\n#lean_audit_end "{file}"\n'
    (work / "AuditBundle.lean").write_text(wrapper)
    env = dict(os.environ)
    env["LEAN_PATH"] = str(work) + (os.pathsep + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")
    version = subprocess.run([args.lean, "--version"], capture_output=True, text=True,
                             check=True, timeout=30).stdout.strip()
    (work / "lean-version.txt").write_text(version + "\n")
    support_rc = run_command([args.lean, "-o", "LeanAuditSupport.olean", "LeanAuditSupport.lean"],
                             work, env, work / "support-build.log", args.timeout)
    if support_rc:
        raise AuditError(f"audit helper build failed ({support_rc}); see {work / 'support-build.log'}")
    rc = run_command([args.lean, "AuditBundle.lean"], work, env, work / "lean-output.log", args.timeout)
    output = (work / "lean-output.log").read_text()
    result = parse_audit_output(output, expected)
    if rc:
        result["errors"].insert(0, f"Lean exited nonzero ({rc})")
    if re.search(r"(?:^|\s)error:", output, re.MULTILINE):
        result["errors"].append("Lean reported an error")
    for hole in source_holes:
        result["errors"].append(f"source proof hole: {hole['file']}:{hole['line']}: {hole['token']}")
    if re.search(r"declaration uses [\"'`‘’“”]*sorry", output):
        result["errors"].append("Lean reported a declaration using sorry")
    result.update({"lean_version": version, "source_manifest": manifest,
                   "scope": "fourteen-file-release" if not args.through else f"partial-through-{args.through}",
                   "allowed_axioms": sorted(ALLOWED_AXIOMS), "lean_returncode": rc,
                   "source_proof_holes": source_holes,
                   "baseline_authored_theorems": sum(len(BASELINE.get(f, [])) for f, _ in targets)})
    baseline_names = {ns + "." + n for f, ns in targets for n in BASELINE.get(f, [])}
    baseline_rows = [d for d in result["declarations"]
                     if d["kind"] == "theorem" and d["user_name"] in baseline_names]
    result["baseline_audit"] = {
        "authored_theorems_found": len(baseline_rows),
        "axiom_free": sum(d["axioms"] == [] for d in baseline_rows),
        "with_axioms": sum(bool(d["axioms"]) for d in baseline_rows),
        "source_hashes_unchanged": all(m["sha256"] == BASELINE_SHA256[m["file"]]
            for m in manifest if m["file"] in BASELINE_SHA256),
    }
    if not args.through:
        baseline_result = result["baseline_audit"]
        if not baseline_result["source_hashes_unchanged"]:
            result["errors"].append("the original three source files differ from their recorded SHA-256 baseline")
        if (baseline_result["authored_theorems_found"], baseline_result["axiom_free"],
                baseline_result["with_axioms"]) != (74, 58, 16):
            result["errors"].append("original theorem audit differs from baseline 74 / 58 axiom-free / 16 with axioms")
    old_files = [v for f,v in result["files"].items() if f in GEOMETRY_BASELINE_SHA256]
    result["geometry_baseline_audit"] = {
        "authored_theorems": sum(v["authored_theorems"] for v in old_files),
        "declarations": sum(v["declarations"] for v in old_files),
        "authored_axiom_free": sum(v["authored_axiom_free"] for v in old_files),
        "authored_with_axioms": sum(v["authored_with_axioms"] for v in old_files),
        "source_hashes_unchanged": all(m["sha256"] == GEOMETRY_BASELINE_SHA256[m["file"]]
            for m in manifest if m["file"] in GEOMETRY_BASELINE_SHA256),
    }
    if not args.through:
        old = result["geometry_baseline_audit"]
        if not old["source_hashes_unchanged"]:
            result["errors"].append("previous seven source files differ from their SHA-256 baseline")
        if (old["authored_theorems"],old["declarations"],old["authored_axiom_free"],
                old["authored_with_axioms"]) != (140,481,69,71):
            result["errors"].append("previous release differs from baseline 140 / 481 / 69 / 71")
    result["result"] = "FAIL" if result["errors"] else "PASS"
    return result

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--source-dir", type=Path, default=PACKAGE / "lean")
    parser.add_argument("--lean", default=os.environ.get("LEAN", "lean"))
    parser.add_argument("--through", choices=[f for f, _ in TARGETS])
    parser.add_argument("--timeout", type=int, default=1200, help="seconds per Lean invocation")
    parser.add_argument("--keep-output", nargs="?", const="", default=os.environ.get("LEAN_AUDIT_OUTPUT_DIR"))
    args = parser.parse_args(argv)
    args.source_dir = args.source_dir.resolve()
    keep = args.keep_output is not None
    if args.keep_output:
        work = Path(args.keep_output).resolve()
        if work.exists() and any(work.iterdir()):
            parser.error(f"output directory is not empty: {work}")
        work.mkdir(parents=True, exist_ok=True)
    else:
        work = Path(tempfile.mkdtemp(prefix="imq-lean-audit-"))
    try:
        result = audit(args, work)
    except (AuditError, OSError, subprocess.SubprocessError) as exc:
        result = {"result": "FAIL", "errors": [str(exc)]}
    (work / "summary.json").write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    print("Lean audit:", result.get("scope", "incomplete"))
    for file, data in result.get("files", {}).items():
        print(f"  {file}: authored theorems={data['authored_theorems']}, "
              f"kernel declarations={data['declarations']}, kernel theorems={data['kernel_theorems']}")
    if "total_declarations" in result:
        print(f"  authored theorems={result['total_authored_theorems']}; "
              f"all declarations={result['total_declarations']}; "
              f"axiom-free declarations={result['axiom_free_declarations']}; "
              f"with-axiom declarations={result['with_axiom_declarations']}")
        print("  axiom sets:", result["axiom_sets"])
        print("  original baseline:", result["baseline_audit"])
        print("  previous release baseline:", result["geometry_baseline_audit"])
    for error in result["errors"]:
        print("FAIL:", error)
    print("RESULT:", result["result"])
    if keep or result["result"] == "FAIL":
        print("Audit artifacts:", work)
    else:
        shutil.rmtree(work)
    return 0 if result["result"] == "PASS" else 1

if __name__ == "__main__":
    sys.exit(main())
