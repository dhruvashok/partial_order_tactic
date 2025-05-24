/-
Copyright (c) 2025 Joseph Qian and Dhruv Ashok. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Qian, Dhruv Ashok
-/
import Lean
import Mathlib.Order.Defs
import Mathlib.Util.AtomM

/-!

# partiarith Tactic

The `partiarith` tactic is created in this file. This tactic, which works over partially ordered
sets, attempts to generate a proof of a the main goal, which must be an inequality between elements
in the partially ordered set. Used as is, the tactic makes use of all hypotheses in the local
context that are inequalities (or equalities) between elements in the partially ordered set.
However, the user can specify which hypotheses from the local context to use, along with proof
terms which might not already be in the local context.

## Implementation Notes

This tactic defines a recognizer `le?`, which is used to check whether or not an Expr is a less-
than-or-equal inequality. It is essentially a macro for `Expr.app3?`.

 * what does "including use of type classes and simp canonical form for new definitions" mean
 * discuss dfs / bfs  choice if/when that's implemented

## References

This code was heavily inspired by the code for the tactic `polyrith`, which was written by
Dhruv Bhatia, who advised me on this project as part of a research project with the Math AI
Lab at the University of Washington.

-/

namespace Mathlib.Tactic.Partiarith
open Lean Meta
open Qq AtomM PrettyPrinter
initialize registerTraceClass `Meta.Tactic.partiarith

@[inline] def le? (p : Expr) : Option (Expr × Expr × Expr) :=
  p.app3? ``LE

/-- Parses local context and hypotheses (provided by client). -/
def parseContext (only: Bool) (hyps: Array Expr) (tgt: Expr) :
    AtomM (Expr × Expr × Array (Expr × (Expr × Expr)) × Array Expr) := do
    let fail {α} : AtomM α := throwError "bad"
    let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars tgt).le? | fail
    let .sort u ← instantiateMVars (← whnf (← inferType α)) | unreachable!
    let some v := u.dec | throwError "not a type{indentExpr α}"
    have α : Q(Type v) := α
    have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
    let rec
    /-- Processes a hypothesis and adds it to the `out` list. -/
    processHyp (ty : Expr) (out: Array (Expr × (Expr × Expr))) := do
      if let some (β, e₁, e₂) := (← instantiateMVars (← inferType ty)).le? then
        -- Check for less-than-equal
        if ← withTransparency (← read).red <| isDefEq α β then
            -- the "atoms" here will eventually be our vertex set
            return out.push (ty, (← addAtom e₁).2, (← addAtom e₂).2)

      -- Check for equalities
      else if let some (β, e₁, e₂) := (← instantiateMVars (← inferType ty)).eq? then
        if ← withTransparency (← read).red <| isDefEq α β then
          let h₁₂ ← mkAppM `le_of_eq #[ty]
          let h₂₁ ← mkAppM `le_of_eq #[(← mkAppM `Eq.symm #[ty])]
          return (out.push (h₁₂, (← addAtom e₁).2, (← addAtom e₂).2)).push (h₂₁, e₂, e₁)
      pure out

    let mut out := #[]
    if !only then
        for ldecl in ← getLCtx do
          out ← processHyp ldecl.toExpr out
    for hyp in hyps do
        out ← processHyp hyp out

    let nodes := (← get).atoms
    pure (e₁, e₂, out, nodes)


structure DfsData where
  pathSoFar : Array (Expr × (Expr × Expr))
  toDiscover : Array (Expr)

/-- Performs a depth-first search over a directed graph representing the local context and user-
defined hypotheses. The nodes of the graph are elements of the poset and the edges represent the ≤
relation, pointing from the smaller element to the larger element. In the case of equality, we use
a bidirectional edge. -/
def dfsOuter (v₁ : Expr) (v₂ : Expr) (edges : Array (Expr × (Expr × Expr))) (nodes : Array Expr)
    (trace := false) : MetaM (Option (Array (Expr × (Expr × Expr)))) := do
  let mut nodes := nodes
  let rec
  /-- Returns an Array containing the outgoing edges of a node `tgt` -/
  getNeighbors (tgt: Expr) : MetaM (Array (Expr × (Expr × Expr))) := do
    let mut out := #[]
    for edge in edges do
      if ← isDefEq edge.2.1 tgt then
        out := out.push edge
    return out

  let rec
  /-- Recursively performs a depth-first search on the directed graph. -/
  dfsLoop (node : Expr) (currentData : DfsData) :
    MetaM (Option (Array (Expr × (Expr × Expr)))) :=
  do
    let neighbors ← getNeighbors node
    for neighbor in neighbors do
    -- only look at undiscovered neighbors
      match currentData.toDiscover.indexOf? neighbor.2.2 with
      | none => continue
      | some i =>
        let currentData := {currentData with toDiscover := currentData.toDiscover.feraseIdx i}
        let addToPath := {currentData with pathSoFar := currentData.pathSoFar.push neighbor}
        if ← isDefEq v₂ neighbor.2.2 then
          -- destination reached
          return (some addToPath.pathSoFar)
        if let some finalData ← dfsLoop neighbor.2.2 addToPath then
          return some finalData -- destination reached at a later step
    -- no neighbors worked: this step is a dead end
    return none
  termination_by currentData.toDiscover.size
  decreasing_by {
    rw [Array.size_feraseIdx]
    apply Nat.sub_one_lt
    apply Nat.ne_of_gt
    apply Fin.size_pos
    exact i
    }

  -- Begin depth-first search.
  let path ← dfsLoop v₁ {pathSoFar := #[], toDiscover := (nodes.erase v₁)}
  -- if trace then logInfo traceString
  return path


def proofFromPath (path : Array (Expr × Expr × Expr)) : Option (MetaM Expr) := do
  let proofs := path.map (fun x => x.1)
  match proofs[0]? with
    | none => none
    | some firstProof =>
    return Array.foldlM (fun a b : Expr => (mkAppM `le_trans #[a, b]))
      firstProof (proofs.erase firstProof)




/-- Given a set of relevant hypotheses (in the local context and/or user-defined hypotheses),
`partiarith` attempts to build a proof of the main goal, which must be an inequality between
elements of a partially ordered set. -/
def partiarith (g : MVarId) (only : Bool) (hyps : Array Expr)
    (traceOnly := false) : MetaM (Except MVarId (Expr)) := do
    g.withContext <| AtomM.run .reducible do
    let (v₁, v₂, edges, nodes) ← parseContext only hyps (← g.getType)
    match ← dfsOuter v₁ v₂ edges nodes traceOnly with
    | some pathToDest => match (proofFromPath pathToDest) with
      | none => return (.error g)
      | some proofProgram =>
      return (.ok (← proofProgram))
    | none => return (Except.error g)

syntax "partiarith" (&" only")? (" [" term,* "]")? : tactic

open Elab Tactic
elab_rules : tactic
  | `(tactic| partiarith $[only%$onlyTk]? $[[$hyps,*]]?) => do
    let hyps ← hyps.map (·.getElems) |>.getD #[] |>.mapM (elabTerm · none)
    let traceMe ← Lean.isTracingEnabledFor `Meta.Tactic.partiarith
    let g ← getMainGoal
    match ← partiarith g onlyTk.isSome hyps traceMe with
    | .ok newGoal =>
      if traceMe then logInfo f!"{← delab newGoal}"
      Lean.Elab.Tactic.closeMainGoal `partiarith newGoal
    | .error g => replaceMainGoal [g]

end Mathlib.Tactic.Partiarith
