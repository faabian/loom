import Auto
import Lean
import Lean.Parser

import Loom.MonadAlgebras.WP.Attr
import Loom.MonadAlgebras.WP.Tactic
-- import Loom.MonadAlgebras.WP.DoNames'
import Loom.MonadAlgebras.WP.Gen
import Loom.Tactic
import Loom.SMT

import CaseStudies.Extension
import CaseStudies.Macro

import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.OfRpcMethod

open Lean
open Lean.Elab
open Lean.Elab.Tactic
open Lean.Meta

private def _root_.Lean.SimpleScopedEnvExtension.get [Inhabited σ] (ext : SimpleScopedEnvExtension α σ)
  [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

private def _root_.Lean.SimplePersistentEnvExtension.get [Inhabited σ] (ext : SimplePersistentEnvExtension α σ)
  [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

private def _root_.Lean.SimplePersistentEnvExtension.modify
  (ext : SimplePersistentEnvExtension α σ) (s : σ -> σ)
  [Monad m] [MonadEnv m] : m Unit := do
  Lean.modifyEnv (ext.modifyState · s)

def getAssertionStx : TacticM (Option Term) := withMainContext do
  let goal <- getMainTarget
  let goalStx <- ppExpr goal
  let ⟨_, ss, ns, _⟩ <- loomAssertionsMap.get
  let .some withNameExpr := goal.find? (fun e => e.isAppOf ``WithName)
    | let .some typeWithNameExpr := goal.find? (fun e => e.isAppOf ``typeWithName)
        | throwError s!"Failed to parse an assertion without names: {goalStx}"
      let nname := typeWithNameExpr.getAppArgs[2]!
      let sname <- nname.getName
      let some id1 := ns[sname]?
        | throwError s!"typeWithName {sname} not registered: {typeWithNameExpr}"
      return some ss[id1]!
  match_expr withNameExpr with
  | WithName exp name =>
    let name <- name.getName
    let some id := ns[name]?
      | let .some typeWithNameExpr := exp.find? (fun e => e.isAppOf ``typeWithName)
          | throwError s!"Failed to prove assertion without names: {goalStx}"
        let nname := typeWithNameExpr.getAppArgs[2]!
        let sname <- nname.getName
        let some id1 := ns[sname]?
          | throwError s!"typeWithName {sname} not registered: {typeWithNameExpr}"
        return some ss[id1]!
    return some ss[id]!
  | _ => throwError s!"Failed to prove assertion which is not registered4: {goalStx}"
  --let ⟨maxId, ss, ns⟩ <- loomAssertionsMap.get

declare_syntax_cat loom_solve_tactic
syntax "loom_solve" : loom_solve_tactic
syntax "loom_solve?" : loom_solve_tactic
syntax "loom_solve!" : loom_solve_tactic
syntax loom_solve_tactic : tactic

syntax "loom_goals_intro" : tactic
syntax "loom_unfold" : tactic
syntax "loom_auto" : tactic
syntax "loom_solver" : tactic
syntax "loom_named_split" : tactic

/-- Phase for loop invariants: entry (before loop), loop (inside loop body), exit (after loop condition fails) -/
inductive LoomPhase where
  | entry : LoomPhase
  | loop : LoomPhase
  | exit : LoomPhase
  deriving Inhabited, BEq

instance : ToString LoomPhase where
  toString
    | .entry => "entry"
    | .loop => "loop"
    | .exit => "exit"

instance : ToMessageData LoomPhase where
  toMessageData p := toString p

/-- Tracking state for phase and if-branch suffix -/
structure PhaseState where
  phase : LoomPhase
  ifBranchSuffix : String := ""
  deriving Inhabited

namespace PhaseState

def toSuffix (ps : PhaseState) : String := toString ps.phase ++ ps.ifBranchSuffix
def withPos (ps : PhaseState) : PhaseState := { ps with ifBranchSuffix := ps.ifBranchSuffix ++ "_pos" }
def withNeg (ps : PhaseState) : PhaseState := { ps with ifBranchSuffix := ps.ifBranchSuffix ++ "_neg" }
def entry : PhaseState := { phase := .entry }
def loop : PhaseState := { phase := .loop }
def exit : PhaseState := { phase := .exit }

end PhaseState

/-- Extract a Name from Lean's Name expression representation -/
private partial def extractLoomName (e : Expr) : Option Name := do
  if e.isAppOfArity ``Name.mkStr 2 then
    let p := e.getAppArgs[0]!
    let s := e.getAppArgs[1]!
    match s with
    | .lit (.strVal s) =>
      match extractLoomName p with
      | some pName => some (Name.mkStr pName s)
      | none => some (Name.mkStr Name.anonymous s)
    | _ => none
  else if e.isAppOf ``Name.anonymous then
    some Name.anonymous
  else
    none

/-- Extract name from WithName expression (name is args[1]) -/
private def extractNameFromWithName (e : Expr) : MetaM Name := do
  let args := e.getAppArgs
  if h : args.size >= 2 then
    match extractLoomName args[1]! with
    | some n => return n
    | none => return Name.anonymous
  else
    return Name.anonymous

/-- Extract name from typeWithName expression (name is args[2]) -/
private def extractNameFromTypeWithName (e : Expr) : MetaM Name := do
  let args := e.getAppArgs
  if h : args.size >= 3 then
    match extractLoomName args[2]! with
    | some n => return n
    | none => return Name.anonymous
  else
    return Name.anonymous

/-- Extract name from MProdWithNames expression (name is args[2], the 3rd type param) -/
private def extractNameFromMProdWithNames (e : Expr) : MetaM Name := do
  let args := e.getAppArgs
  -- MProdWithNames α β αName has 3 args: args[0] = α, args[1] = β, args[2] = αName
  if h : args.size >= 3 then
    match extractLoomName args[2]! with
    | some n =>
      -- Extract just the last string component if it's a compound name
      match n with
      | .str _ s => return Name.mkSimple s
      | _ => return n
    | none => return Name.anonymous
  else
    return Name.anonymous

/-- Helper to check if expression is an application of a given short name (handles namespaces) -/
private def isAppOfShortName (e : Expr) (shortName : String) : Bool :=
  let matchesShortName (name : Name) : Bool :=
    let s := name.toString
    s == shortName || s.endsWith ("." ++ shortName)
  if e.isApp then
    e.getAppFn.constName?.any matchesShortName
  else if e.isConst then
    matchesShortName e.constName!
  else
    false
/-- Recursively extract ALL names from nested MProdWithNames and WithName types.
    Used for full destructuring of state tuples.
    Note: The returned names are "base" names - collision handling with existing hypotheses
    is done by getUnusedUserName when these names are actually used in loom_prod_split. -/
private partial def getAllNamesFromMProdWithNamesAndWithName (e : Expr)
    (lastNamedField : Name := `state) (usedSuffixes : Std.HashMap String Nat := {})
    : MetaM (List Name × Std.HashMap String Nat) := do
  let e := e.consumeMData

  -- Handle MProdWithNames
  if isAppOfShortName e "MProdWithNames" then
    let args := e.getAppArgs
    if args.size < 3 then return ([], usedSuffixes)
    -- Extract fst name (args[2])
    let fstName ← match extractLoomName args[2]! with
      | some (.str _ s) => pure (Name.mkSimple s)
      | some n => pure n
      | none => pure `_fst
    -- Recurse into snd type (args[1])
    let (sndNames, updatedSuffixes) ← getAllNamesFromMProdWithNamesAndWithName args[1]! fstName usedSuffixes
    match sndNames with
    | [] =>
      -- Fallback for unnamed snd: use fstName_N where N avoids collisions
      let baseStr := fstName.toString
      let currentSuffix := updatedSuffixes.getD baseStr 1
      let sndFallback := Name.mkSimple s!"{baseStr}_{currentSuffix}"
      let newSuffixes := updatedSuffixes.insert baseStr (currentSuffix + 1)
      return ([fstName, sndFallback], newSuffixes)
    | _ => return (fstName :: sndNames, updatedSuffixes)

  -- Handle WithName
  else if isAppOfShortName e "WithName" then
    let args := e.getAppArgs
    if args.size >= 2 then
      match extractLoomName args[1]! with
      | some (.str _ s) => return ([Name.mkSimple s], usedSuffixes)
      | some n => return ([n], usedSuffixes)
      | none =>
        -- Fallback: use lastNamedField_N where N avoids collisions
        let baseStr := lastNamedField.toString
        let currentSuffix := usedSuffixes.getD baseStr 1
        let fallbackName := Name.mkSimple s!"{baseStr}_{currentSuffix}"
        let newSuffixes := usedSuffixes.insert baseStr (currentSuffix + 1)
        return ([fallbackName], newSuffixes)
    else
      let baseStr := lastNamedField.toString
      let currentSuffix := usedSuffixes.getD baseStr 1
      let fallbackName := Name.mkSimple s!"{baseStr}_{currentSuffix}"
      let newSuffixes := usedSuffixes.insert baseStr (currentSuffix + 1)
      return ([fallbackName], newSuffixes)

  else
    return ([], usedSuffixes)

/-- Known clause type prefixes that can appear in hypothesis names -/
private def clausePrefixes : List String := ["inv.", "done.", "assert.", "dec.", "req.", "ens.", "choice."]

/-- Check if a name is an invariant -/
private def isInvariantName (n : Name) : Bool := n.toString.startsWith "inv."

/-- Strip clause type prefix from a name -/
private def stripClausePrefix (n : Name) : Name :=
  let s := n.toString
  match clausePrefixes.find? (s.startsWith ·) with
  | some p => Name.mkSimple (s.drop p.length)
  | none => n

/-- Analyze clause type for if_pos/if_neg detection, returning (needsPhaseChange, strippedName) -/
private def analyzeClauseType (n : Name) : (Bool × Name) :=
  let stripped := stripClausePrefix n
  match stripped with
  | `if_pos => (true, stripped)
  | `if_neg => (true, stripped)
  | _ => (false, stripped)

/-- Phases seen for an invariant base name allocation -/
structure InvariantCacheEntry where
  baseName : Name
  phasesSeen : List LoomPhase := []
  deriving Inhabited

/-- State for tracking used goal names during structural split -/
structure SplitState where
  usedBaseNames : Std.HashMap String Nat := {}  -- base name -> count for deduplication
  invariantCache : Std.HashMap String InvariantCacheEntry := {}  -- raw inv name -> (base, phases seen)
  deriving Inhabited

/-- Get a unique base name, deduplicating if necessary -/
private def getUniqueBaseName (baseName : Name) : StateT SplitState TacticM Name := do
  let state ← get
  let baseStr := baseName.toString
  let count := state.usedBaseNames.getD baseStr 0
  set { state with usedBaseNames := state.usedBaseNames.insert baseStr (count + 1) }
  if count == 0 then
    return baseName
  else
    return Name.mkSimple s!"{baseStr}_{count}"

/-- Add phase suffix to base name -/
private def addPhaseSuffix (baseName : Name) (ps : PhaseState) : Name :=
  Name.mkStr baseName ps.toSuffix

/-- Process a goal name with deduplication. For invariants, caches the base name so all phases share it.
    The key insight: use JUST the raw name as the cache key for base name allocation.
    This ensures the same invariant (e.g., outer_bound) gets the same base name regardless of which
    phase/suffix it appears with. The full suffix (phase + if-branch) is added at the end. -/
private def processGoalNameWithDedup (n : Name) (ps : PhaseState) : StateT SplitState TacticM Name := do
  let isInv := isInvariantName n
  let stripped := stripClausePrefix n

  if isInv then
    let state ← get
    let rawStr := n.toString
    match state.invariantCache[rawStr]? with
    | some entry =>
      -- We've seen this raw name before → reuse the same base name
      -- No need to track phases - the same invariant should always share the base name
      return addPhaseSuffix entry.baseName ps
    | none =>
      -- First time seeing this raw name → allocate new base name
      let uniqueBase ← getUniqueBaseName stripped
      let newEntry : InvariantCacheEntry := { baseName := uniqueBase, phasesSeen := [] }
      modify fun s => { s with invariantCache := s.invariantCache.insert rawStr newEntry }
      return addPhaseSuffix uniqueBase ps
  else
    -- For non-invariants, just get unique base name
    getUniqueBaseName stripped

/-- Classification of goal structure for traversal -/
private inductive GoalKind where
  | forallWithName (rawName : Name) (strippedName : Name)
  | forallTypeWithName (rawName : Name) (strippedName : Name)
  | forallMProdWithNames (varName : Name)
  | forallOther (bindingName : Name)
  | andGoal
  | withNameGoal (name : Name)
  | typeWithNameGoal (name : Name)
  | arrowWithName (rawName : Name) (strippedName : Name)
  | arrowTypeWithName (rawName : Name) (strippedName : Name)
  | arrowOther
  | other

/-- Classify a goal type into its structural kind -/
private def classifyGoalType (goalType : Expr) : MetaM GoalKind := do
  match goalType with
  | .forallE bindingName domain _ _ =>
    let domain := domain.consumeMData
    if isAppOfShortName domain "WithName" then
      let rawName ← extractNameFromWithName domain
      let (_, strippedName) := analyzeClauseType rawName
      return if goalType.isArrow then .arrowWithName rawName strippedName
             else .forallWithName rawName strippedName
    else if isAppOfShortName domain "typeWithName" then
      let rawName ← extractNameFromTypeWithName domain
      let (_, strippedName) := analyzeClauseType rawName
      return if goalType.isArrow then .arrowTypeWithName rawName strippedName
             else .forallTypeWithName rawName strippedName
    else if isAppOfShortName domain "MProdWithNames" then
      let varName ← extractNameFromMProdWithNames domain
      return .forallMProdWithNames varName
    else
      return if goalType.isArrow then .arrowOther else .forallOther bindingName
  | _ =>
    if isAppOfShortName goalType "And" then
      return .andGoal
    else if isAppOfShortName goalType "WithName" then
      let name ← extractNameFromWithName goalType
      return .withNameGoal name
    else if isAppOfShortName goalType "typeWithName" then
      let name ← extractNameFromTypeWithName goalType
      return .typeWithNameGoal name
    else
      return .other

/-- Intro a hypothesis with a fresh name and continue traversal -/
private def introAndContinue (baseName : Name) (ps : PhaseState) (pendingLoopCond : Bool)
    (cont : PhaseState → Bool → StateT SplitState TacticM Unit) : StateT SplitState TacticM Unit := do
  let freshName ← getUnusedUserName baseName
  let freshIdent := mkIdent freshName
  evalTactic $ ← `(tactic| intro $freshIdent:ident)
  cont ps pendingLoopCond

/-- Handle if_pos/if_neg intro with phase transitions -/
private def introIfBranch (isPos : Bool) (ps : PhaseState) (pendingLoopCond : Bool)
    (cont : PhaseState → Bool → StateT SplitState TacticM Unit) : StateT SplitState TacticM Unit := do
  let baseName := if isPos then `if_pos else `if_neg
  let freshName ← getUnusedUserName baseName
  let freshIdent := mkIdent freshName
  evalTactic $ ← `(tactic| intro $freshIdent:ident)
  if pendingLoopCond then
    cont (if isPos then PhaseState.loop else PhaseState.exit) false
  else
    cont (if isPos then ps.withPos else ps.withNeg) false

/-- Main recursive traversal and splitting function with state for name deduplication -/
private partial def traverseAndSplitWithState (ps : PhaseState) (pendingLoopCond : Bool := false) : StateT SplitState TacticM Unit := do
  let goals ← getGoals
  if goals.isEmpty then return

  let goal ← getMainGoal
  let goalTypeRaw ← goal.getType
  let goalType ← instantiateMVars goalTypeRaw
  let goalType := goalType.consumeMData

  match ← classifyGoalType goalType with
  | .forallWithName _ strippedName =>
    match strippedName with
    | `if_pos => introIfBranch true ps pendingLoopCond (fun ps plc => traverseAndSplitWithState ps plc)
    | `if_neg => introIfBranch false ps pendingLoopCond (fun ps plc => traverseAndSplitWithState ps plc)
    | _ => introAndContinue strippedName ps pendingLoopCond (fun ps plc => traverseAndSplitWithState ps plc)

  | .forallTypeWithName _ strippedName =>
    introAndContinue strippedName ps pendingLoopCond (fun ps plc => traverseAndSplitWithState ps plc)

  | .forallMProdWithNames varName =>
    let tempName ← getUnusedUserName `_mprod
    let tempIdent := mkIdent tempName
    evalTactic $ ← `(tactic| intro $tempIdent:ident)
    if varName != Name.anonymous then
      let fstName ← getUnusedUserName varName
      -- Use underscore separator instead of dot to avoid creating hierarchical names
      let sndBaseName := Name.mkSimple s!"{varName}_snd"
      let sndName ← getUnusedUserName sndBaseName
      let fstIdent := mkIdent fstName
      let sndIdent := mkIdent sndName
      evalTactic $ ← `(tactic| obtain ⟨$fstIdent:ident, $sndIdent:ident⟩ := $tempIdent:ident)
      evalTactic $ ← `(tactic| try simp only [MProdWithNames.fst, MProdWithNames.snd] at *)
    traverseAndSplitWithState PhaseState.entry true

  | .forallOther bindingName =>
    let baseName := if bindingName == Name.anonymous then `h else bindingName
    introAndContinue baseName ps pendingLoopCond (fun ps plc => traverseAndSplitWithState ps plc)

  | .andGoal =>
    let parentTag ← goal.getTag
    evalTactic $ ← `(tactic| apply And.intro)
    let newGoals ← getGoals
    if parentTag != Name.anonymous then
      for g in newGoals do
        let gTag ← g.getTag
        if gTag == Name.anonymous then
          g.setTag parentTag
    let mut processedGoals : List MVarId := []
    for g in newGoals do
      setGoals [g]
      try
        traverseAndSplitWithState ps pendingLoopCond
      catch _ =>
        pure ()
      processedGoals := processedGoals ++ (← getGoals)
    setGoals processedGoals

  | .withNameGoal name =>
    let uniqueName ← processGoalNameWithDedup name ps
    goal.setTag uniqueName
    evalTactic $ ← `(tactic| unfold WithName)
    traverseAndSplitWithState ps pendingLoopCond

  | .typeWithNameGoal name =>
    let uniqueName ← processGoalNameWithDedup name ps
    goal.setTag uniqueName
    evalTactic $ ← `(tactic| unfold typeWithName)
    traverseAndSplitWithState ps pendingLoopCond

  | .arrowWithName _ strippedName =>
    match strippedName with
    | `if_pos => introIfBranch true ps pendingLoopCond (fun ps plc => traverseAndSplitWithState ps plc)
    | `if_neg => introIfBranch false ps pendingLoopCond (fun ps plc => traverseAndSplitWithState ps plc)
    | _ => introAndContinue strippedName ps pendingLoopCond (fun ps plc => traverseAndSplitWithState ps plc)

  | .arrowTypeWithName _ strippedName =>
    introAndContinue strippedName ps pendingLoopCond (fun ps plc => traverseAndSplitWithState ps plc)

  | .arrowOther =>
    introAndContinue `h ps pendingLoopCond (fun ps plc => traverseAndSplitWithState ps plc)

  | .other =>
    pure ()

/-- Entry point for traverseAndSplit - initializes state with given phase -/
private def traverseAndSplit (phase : LoomPhase) : TacticM Unit := do
  let ps : PhaseState := { phase := phase }
  let ((), _) ← traverseAndSplitWithState ps |>.run {}
  -- After splitting, clean up any inaccessible hypothesis names using Lean's built-in exposeNames
  let goals ← getGoals
  let mut processedGoals : List MVarId := []
  for g in goals do
    try
      -- Use Lean's MVarId.exposeNames which automatically renames all inaccessible hypotheses
      let g' ← g.exposeNames
      processedGoals := processedGoals ++ [g']
    catch _ =>
      -- If exposing names fails, keep the original goal
      processedGoals := processedGoals ++ [g]
  setGoals processedGoals

elab_rules : tactic
  | `(tactic| loom_named_split) => withMainContext do
    traverseAndSplit .entry

/-- Post-process hypotheses with MProdWithNames types by fully destructuring them.
    This handles nested MProdWithNames and WithName types that weren't fully destructured
    during the main traversal. This is sound albeit hacky and ideally should be implemented within the traversal itself.
    Uses revert + simp[forall_intro] + intro approach:
    1. Revert the hypothesis (moves it to the goal as ∀)
    2. Simp with MProdWithNames.forall_intro (unfolds ∀ x : MProd, P x → ∀ a b, P ⟨a,b⟩)
    3. Intro with the extracted names
    This avoids obtain/cases which would add .mk suffix to goal names. -/
syntax "loom_prod_split" : tactic

elab_rules : tactic
  | `(tactic| loom_prod_split) => withMainContext do
    let lctx ← getLCtx
    let mut hypsToProcess : Array (LocalDecl × List Name) := #[]

    -- First pass: collect hypotheses to process
    for ldecl in lctx do
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      let ty := ty.consumeMData
      if isAppOfShortName ty "MProdWithNames" then
        let (allNames, _) ← getAllNamesFromMProdWithNamesAndWithName ty
        if allNames.length > 1 then
          hypsToProcess := hypsToProcess.push (ldecl, allNames)

    -- Second pass: process each hypothesis using revert + simp + intro
    for (ldecl, allNames) in hypsToProcess do
      -- Use withMainContext to refresh the context and see newly introduced hypotheses
      -- This ensures getUnusedUserName properly avoids collisions with names from previous iterations
      withMainContext do
        let freshNames ← allNames.mapM getUnusedUserName
        let nameIdents := freshNames.map Lean.mkIdent |>.toArray

        try
          -- Step 1: Revert the hypothesis (moves it to the goal as a forall)
          -- This also reverts any hypotheses that depend on it
          let goal ← getMainGoal
          let (revertedFVars, newGoal) ← goal.revert #[ldecl.fvarId]
          let numReverted := revertedFVars.size
          setGoals [newGoal]

          -- Step 2: Simp with forall_intro to unfold ∀ x : MProdWithNames, P x → ∀ a b, P ⟨a,b⟩
          -- Only apply to the goal (not at *) to avoid affecting other hypotheses
          evalTactic (← `(tactic| simp only [MProdWithNames.forall_intro, WithName.erase, WithName.mk']))

          -- Step 3: Intro with the proper names for the MProdWithNames components
          evalTactic (← `(tactic| intro $[$nameIdents]*))

          -- Step 4: Intro the remaining hypotheses that were reverted along with the main one
          -- The number of additional intros needed is: numReverted - 1 (we already handled the MProd)
          let remainingIntros := numReverted - 1
          if remainingIntros > 0 then
            -- Use introNP to introduce the remaining hypotheses while preserving their names
            let goal ← getMainGoal
            let (_, newGoal) ← goal.introNP remainingIntros
            setGoals [newGoal]
        catch _ =>
          -- If the revert+simp+intro approach fails, skip this hypothesis
          pure ()

    -- Clean up any remaining types with simp
    evalTactic (← `(tactic| try simp only [MProdWithNames.fst, MProdWithNames.snd, WithName.mk', WithName.erase] at *))

elab_rules : tactic
  | `(tactic| loom_goals_intro) => withMainContext do
    let vlsIntro <- `(tactic| (
      wpgen
      try simp only [loomWpSimp]
      try unfold spec
      try simp only [invariantSeq]
      try simp only [List.foldr]
      try simp only [loomLogicSimp]
      try simp only [iSup_apply, iSup_Prop_eq, exists_and_left, exists_and_right,
                     iInf_apply, iInf_Prop_eq, forall_and_left, forall_and_right]
    ))
    evalTactic vlsIntro

elab_rules : tactic
  | `(tactic| loom_unfold) => withMainContext do
    -- Use unfold for the type abbreviations, then simp for constructors/projections
    -- The try blocks ensure we don't fail if a term doesn't appear
    let vlsUnfold <- `(tacticSeq|
      all_goals try unfold WithName at *
      all_goals try unfold typeWithName at *
      all_goals try unfold MProdWithNames at *
      all_goals try simp only [WithName.mk', WithName.erase, typeWithName.erase,
                               MProdWithNames.mk', MProdWithNames.fst, MProdWithNames.snd,
                               MProdWithNames.mk.injEq, and_imp] at *)
    evalTactic vlsUnfold

elab_rules : tactic
  | `(tactic| loom_auto) => withMainContext do
    let ctx := (<- solverHints.get)
    let mut hints : Array (TSyntax ``Auto.hintelem) := #[]
    for c in ctx do
      hints := hints.push $ <- `(Auto.hintelem| $(mkIdent c):ident)
    hints := hints.push $ <- `(Auto.hintelem| *)
    let vlsAuto <- `(tactic| try (try simp only [loomAbstractionSimp] at *); loom_smt [$hints,*])
    evalTactic vlsAuto

elab_rules : tactic
  | `(tactic| $vls:loom_solve_tactic) => withMainContext do
    let vlsTryThis <- `(tacticSeq|
        loom_goals_intro
        loom_named_split
        all_goals loom_prod_split
        all_goals loom_unfold
        all_goals loom_solver)
    if let `(loom_solve_tactic| loom_solve?) := vls then
      Tactic.TryThis.addSuggestion (<-getRef) vlsTryThis
    else
      let vlsIntro ← `(tactic| loom_goals_intro)
      let vlsSplit ← `(tactic| loom_named_split)
      let vlsDestructure ← `(tactic| all_goals loom_prod_split)
      let vlsUnfold ← `(tactic| all_goals loom_unfold)
      let vlsSolve ← `(tactic| all_goals loom_solver)
      evalTactic vlsIntro
      evalTactic vlsSplit
      evalTactic vlsDestructure
      evalTactic vlsUnfold
      -- Only collect goal info for loom_solve! (error reporting)
      let isStrict := match vls with
        | `(loom_solve_tactic| loom_solve!) => true
        | _ => false
      let mut res : List (MVarId × Option Term) := []
      if isStrict then
        let ⟨_, _, ns, _⟩ <- loomAssertionsMap.get
        for mvarId in (← getGoals) do
          setGoals [mvarId]
          let stx_res <- try getAssertionStx catch _ => pure none
          let tag <- mvarId.getTag
          let isDerived := ns.contains tag || ns.toList.any fun (n, _) =>
            let s := tag.toString
            let p := n.toString
            s.startsWith (p ++ "_") || s.startsWith (p ++ ".")
          let isEnsures := ns.contains (Name.mkStr (Name.mkSimple "ensures") tag.toString)
          if stx_res.isSome || isDerived || isEnsures then
            res := res ++ [(mvarId, stx_res)]
          else
            res := res ++ [(mvarId, none)]
      -- Run solver on all goals
      evalTactic vlsSolve
      -- Report errors for loom_solve!
      if isStrict then
        let unsolvedGoals ← getGoals
        for (mvarId, stx_res) in res do
          if unsolvedGoals.contains mvarId then
            match stx_res with
            | some stx => logErrorAt stx $ m!"Failed to prove assertion\n{mvarId}"
            | none => logError m!"Failed to prove nameless assertion\n{mvarId}"

elab "loom_solve?" : tactic => withMainContext do
  let ctx := (<- solverHints.get)
  let mut hints : Array (TSyntax ``Auto.hintelem) := #[]
  for c in ctx do
    hints := hints.push $ <- `(Auto.hintelem| $(mkIdent c):ident)
  -- hints := hints.push $ <- `(Auto.hintelem| *)
  let tac <- `(tactic| (
  intro
  try simp only [$(mkIdent `loomAbstractionSimp):ident] at *
  wpgen
  try simp only [$(mkIdent `loomWpSimp):ident]
  try simp only [$(mkIdent ``WithName):ident]
  try simp only [$(mkIdent ``typeWithName):ident]
  try unfold spec
  try simp only [$(mkIdent ``invariantSeq):ident]
  try simp only [$(mkIdent ``WithName.mk'):ident]
  try simp only [$(mkIdent ``WithName.erase):ident]
  try simp only [$(mkIdent ``typeWithName.erase):ident]
  try simp only [$(mkIdent ``List.foldr):ident]
  try simp only [$(mkIdent `loomLogicSimp):ident]
  try simp only [$(mkIdent `simpMAlg):ident]
  repeat' (apply $(mkIdent ``And.intro) <;> (repeat loom_intro))
  any_goals loom_smt [$hints,*]
  ))
  Tactic.TryThis.addSuggestion (<-getRef) tac

elab_rules : tactic
  | `(tactic| loom_solver) => withMainContext do
    let opts <- getOptions
    let solver := opts.getString (defVal := "grind") `loom.solver
    match solver with
      | "grind" =>
        /- In case of `grind` solver, we need  to fetch the number of splits from the options first. -/
        let splits := Lean.Syntax.mkNatLit <| (opts.getNat (defVal := 20) `loom.solver.grind.splits)
        evalTactic $ <- `(tactic| try grind ($(mkIdent `splits):ident := $splits))
      | "custom" =>
        evalTactic $ <- `(tactic| fail "Custom solver is not specified")
      | _ => evalTactic $ <- `(tactic| loom_auto)
