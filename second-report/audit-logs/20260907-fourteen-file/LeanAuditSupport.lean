import Lean.Elab.Print
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
