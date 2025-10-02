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

/-- A recognizer for ≤ -/
@[inline] def le? (p : Expr) : Option (Expr × Expr × Expr) :=
  p.app3? ``LE

/-! # DFS helper functions -/

/-- Parses local context and hypotheses (provided by client). -/
def parseContext (only: Bool) (hyps: Array Expr) (tgt: Expr) :
    AtomM (Expr × Expr × Array (Expr × (Expr × Expr)) × Array Expr) := do
    let fail {α} : AtomM α := throwError "bad goal: main goal must be of the form a ≤ b or a ≥ b"
    let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars tgt).le? | fail
    let .sort u ← instantiateMVars (← whnf (← inferType α)) | unreachable!
    let some v := u.dec | throwError "not a type{indentExpr α}"
    have α : Q(Type v) := α
    have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
    let rec
    /-- Parses a hypothesis and adds it to the `out` list. -/
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

/-- A representation of the current state of the DFS traversal -/
structure DfsData where
  /-- An Array containing the hypotheses in the path that has been built so far. -/
  pathSoFar : Array (Expr × (Expr × Expr))
  /-- An Array of the terms that have not yet been discovered by the DFS algorithm. -/
  toDiscover : Array (Expr)

/-- Performs a depth-first search over a directed graph representing the local context
 -- and user-defined hypotheses. The nodes of the graph are elements of the poset and
 -- the edges represent the ≤ relation, pointing from the smaller element to the larger
 -- element. In the case of equality, we use a bidirectional edge. -/
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

  /-- Recursively performs depth-first search on the directed graph. -/
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

/-- Recursively performs breadth-first search on the directed graph. -/
def bfs (v₁ : Expr) (v₂ : Expr) (domain : Array Expr) (to_visit : List $ (Expr × (Expr × Expr)) ×
    Array (Expr × (Expr × Expr))) (edges : Array (Expr × (Expr × Expr))) (_h : domain.size ≠ 0) :
    OptionT MetaM $ Array (Expr × (Expr × Expr)) := do
  let in_domain ← to_visit.filterM λe => domain.anyM (isDefEq e.1.2.2 .)
  let lift {α : Type} (o : Option α) := OptionT.mk $ pure o

  match in_domain with
    | List.nil => lift none
    | List.cons ⟨x, path⟩ xs =>
      let path' := path ++ [x]

      if ← isDefEq x.2.2 v₂ then
        lift $ some path'
      else
        let children ← edges.filterM λe => isDefEq e.2.1 x.2.2
        let domain' := domain.feraseIdx $ ← domain.indexOf? x.2.2|> lift
        if h₁ : domain'.size ≠ 0 then
          bfs v₁ v₂ domain' (xs ++ children.toList.map (⟨., path'⟩)) edges h₁
        else
          lift none
termination_by domain.size
decreasing_by (
  rw [Array.size_feraseIdx]
  exact Nat.sub_one_lt _h
)

/-- Find all edges starting from a given node. -/
def bfsOuter (v₁ : Expr) (v₂ : Expr) (edges : Array (Expr × (Expr × Expr))) (nodes : Array Expr)
    (trace := false) : MetaM (Option (Array (Expr × (Expr × Expr)))) := do
  let nodes' := nodes.erase v₁
  if h : nodes'.size ≠ 0 then
    let children ← edges.filterM λe => isDefEq e.2.1 v₁
    bfs v₁ v₂ nodes' (children.toList.map λe => ⟨e, ⟨[]⟩⟩) edges h
  else
    pure none

/-- Generates the proof of a path generated by `dfsOuter` or `bfsOuter`. -/
def proofFromPath (path : Array (Expr × Expr × Expr)) : Option (MetaM Expr) := do
  let proofs := path.map (fun x => x.1)
  match proofs[0]? with
    | none => none
    | some firstProof =>
    return Array.foldlM (fun a b : Expr => (mkAppM `le_trans #[a, b]))
      firstProof (proofs.erase firstProof)


/-! # Main function -/

/--
This is the main body of the `partiarith` tactic. It takes in the following inputs:
* `g : MVarId` - the main goal
* `only : Bool` - This represents whether the user used the keyword "only"
* `is_bfs : Bool` - This represents whether the user used the keyword "bfs"
* `hyps : Array Expr` - the hypotheses/proof terms selected by the user
* `traceOnly : Bool` - If enabled, the returned syntax will be `.missing`

First, the tactic verifies that `g` is an inequality between two terms of the same type, and throws
an error if this is not the case. Then, it collects all relevant hypotheses/proof terms from the
local context and from those selected by the user, taking into account whether `only` is true.
The hypotheses are added to an `Array` and all unique terms in the hypotheses are added
to a list of atoms.

The tactic then performs an algorithmic search over the `Array` of hypotheses in order to find a
path between the two terms in the main goal. The tactic uses a depth-first search algorithm by
default, and uses a breadth-first search algorithm if `is_bfs` is true. The resulting path is a
sequence of inequalities, either all less than or equal or all greater than or equal statements.
The `Array` is designed to contain all of the information that would normally be stored in a graph
representation of the hypotheses, where hypotheses are edges and the terms are nodes.

If a path is found, the tactic converts it into a proof of the main goal via transitivity, and uses
it to close the main goal. Otherwise, return `.error g` if no path was found or if a proof could
not be made from the path.
-/
def partiarith (g : MVarId) (only : Bool) (is_bfs : Bool) (hyps : Array Expr)
    (traceOnly := false): MetaM (Except MVarId (Expr)) := do
  g.withContext <| AtomM.run .reducible do
  let (v₁, v₂, edges, nodes) ← parseContext only hyps (← g.getType)
  match ← (if is_bfs then bfsOuter else dfsOuter) v₁ v₂ edges nodes with
  | some pathToDest => match (proofFromPath pathToDest) with
    | none => return (.error g)
    | some proofProgram =>
      return (.ok (← proofProgram))
  | none => return (Except.error g)

/--
Attempts to prove a user-specified inequality in a partially ordered set by transitivity on
hypotheses in the local context (and additional proof terms if the user specifies them). If
successful, the main goal will be closed.

* `partiarith` will use all relevant hypotheses in the local context.
* `partiarith [t1, t2, t3]` will add proof terms t1, t2, t3 to the local context.
* `partiarith only [h1, h2, h3, t1, t2, t3]` will use only local hypotheses.
  `h1`, `h2`, `h3`, and proofs `t1`, `t2`, `t3`. It will ignore the rest of the local context.
* `partiarith bfs` will attempt to close the goal using a breadth-first searching algorithm instead
  of a depth-first searching algorithm (default).

Examples:

```lean
example (a b c : α) [PartialOrder α] (hab : a ≤ b) (hbc : b ≤ c) :
    a ≤ c := by
  partiarith

example (a b c : α) [PartialOrder α] (hab : a = b) (hbc : b = c) :
    a ≤ c := by
  partiarith

example (a b c d e: α) [PartialOrder α] (hab : a ≤ b) (hac : a ≤ c) (hbc : c = b)
    (hbd : b ≤ d) (hce : c ≤ e) : a ≤ e := by
  partiarith only [hab, hbc, hce]

example (a b c : α) [PartialOrder α] (hab : a ≤ b) (hbc : b ≤ c) :
    a ≤ c := by
  partiarith bfs
```
-/
syntax "partiarith" (&" only")? (&" bfs")? (" [" term,* "]")? : tactic

open Elab Tactic
elab_rules : tactic
  | `(tactic| partiarith $[only%$onlyTk]? $[bfs%$bfsTk]? $[[$hyps,*]]?) => do
    let hyps ← hyps.map (·.getElems) |>.getD #[] |>.mapM (elabTerm · none)
    let traceMe ← Lean.isTracingEnabledFor `Meta.Tactic.partiarith
    let g ← getMainGoal
    match ← partiarith g onlyTk.isSome bfsTk.isSome hyps traceMe with
    | .ok newGoal =>
      if traceMe then logInfo f!"{← delab newGoal}"
      Lean.Elab.Tactic.closeMainGoal `partiarith newGoal
    | .error g => replaceMainGoal [g]

end Mathlib.Tactic.Partiarith
