import Lean.Elab.Command
import Lean.Meta.Eval
import Plausible.Gen
import Plausible.Sampleable


open Plausible


open SampleableExt

/--
Print (at most) 10 samples of a given type to stdout for debugging.
Output examples are separated by two newlines.
-/
def printSamples2 {t : Type} [Repr t] (g : Gen t) : IO PUnit := do
  let xs := List.range 10
  for x in xs do
    try
      let y ← Gen.run g x
      IO.println s!"{repr y}\n"
    catch
      | .userError msg => IO.println s!"{msg}\n"
      | e => throw e


open Lean Meta Elab

private def mkGenerator (e : Expr) : MetaM (Level × Expr × Expr × Expr) := do
  let exprTyp ← inferType e
  let .sort u ← whnf (← inferType exprTyp) | throwError m!"{exprTyp} is not a type"
  let .succ u := u | throwError m!"{exprTyp} is not a type with computational content"
  match_expr exprTyp with
  | Gen α =>
    let reprInst ← synthInstance (mkApp (mkConst ``Repr [u]) α)
    return ⟨u, α, reprInst, e⟩
  | _ =>
    let v ← mkFreshLevelMVar
    let sampleableExtInst ← synthInstance (mkApp (mkConst ``SampleableExt [u, v]) e)
    let v ← instantiateLevelMVars v
    let reprInst := mkApp2 (mkConst ``SampleableExt.proxyRepr [u, v]) e sampleableExtInst
    let gen := mkApp2 (mkConst ``SampleableExt.sample [u, v]) e sampleableExtInst
    let typ := mkApp2 (mkConst ``SampleableExt.proxy [u, v]) e sampleableExtInst
    return ⟨v, typ, reprInst, gen⟩



elab "#samplenl " e:term : command =>
  Command.runTermElabM fun _ => do
    let e ← Elab.Term.elabTermAndSynthesize e none
    let ⟨_, α, repr, gen⟩ ← mkGenerator e
    let printSamples := mkApp3 (mkConst ``printSamples2 []) α repr gen
    let code ← unsafe evalExpr (IO PUnit) (mkApp (mkConst ``IO) (mkConst ``PUnit [1])) printSamples
    _ ← code

