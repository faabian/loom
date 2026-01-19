import Auto

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
set_option loom.solver.grind.splits 5
set_option maxHeartbeats 0

-- Definitions for the problem domain

def Move := Int × Int

instance : Inhabited Move := ⟨(0, 0)⟩

def knightMoves : List Move := [
  (2, 1), (2, -1), (-2, 1), (-2, -1),
  (1, 2), (1, -2), (-1, 2), (-1, -2)
]

-- Specification of a valid path
inductive ValidPath : (Int × Int) → (Int × Int) → Nat → Prop where
  | zero : ValidPath p p 0
  | step {p1 p2 p3 n} :
      ValidPath p1 p2 n →
      (p3.1 - p2.1, p3.2 - p2.2) ∈ knightMoves →
      ValidPath p1 p3 (n + 1)

-- Shortest path specification
def IsShortestDistance (start target : Int × Int) (d : Nat) : Prop :=
  ValidPath start target d ∧ ∀ d', ValidPath start target d' → d ≤ d'

def IsSorted (q : List (Int × Int × Nat)) : Prop :=
  List.Chain' (· ≤ ·) (q.map (fun (_, _, d) => d))

def AllValidPaths (q : List (Int × Int × Nat)) (start : Int × Int) : Prop :=
  ∀ x y d, (x, y, d) ∈ q → ValidPath start (x, y) d

def QueueShortest (q : List (Int × Int × Nat)) (start : Int × Int) : Prop :=
  ∀ x y d, (x, y, d) ∈ q → ∀ d', ValidPath start (x, y) d' → d ≤ d'

def VisitedComplete (visited : List (Int × Int)) (start : Int × Int) (limit : Nat) : Prop :=
  ∀ x y k, ValidPath start (x, y) k → k ≤ limit → (x, y) ∈ visited

def VisitedCompleteQueue (visited : List (Int × Int)) (start : Int × Int) (q : List (Int × Int × Nat)) : Prop :=
  match q with
  | [] => True
  | (_, _, d) :: _ => VisitedComplete visited start d

def ClosedSet (visited : List (Int × Int)) (queue : List (Int × Int × Nat)) : Prop :=
  ∀ x y, (x, y) ∈ visited →
    (∃ d, (x, y, d) ∈ queue) ∨
    (∀ nx ny, (nx - x, ny - y) ∈ knightMoves → (nx, ny) ∈ visited)

-- The method
method min_knight_moves (sx : Int) (sy : Int) (tx : Int) (ty : Int) return (dist : Option Nat)
  ensures match dist with | some d => IsShortestDistance (sx, sy) (tx, ty) d | none => True
  do
    let mut queue : List (Int × Int × Nat) := [(sx, sy, 0)]
    let mut visited : List (Int × Int) := [(sx, sy)]
    let mut found_dist : Option Nat := none

    while !queue.isEmpty ∧ found_dist.isNone
      invariant all_valid : AllValidPaths queue (sx, sy)
      invariant queue_shortest : QueueShortest queue (sx, sy)
      invariant sorted : IsSorted queue
      invariant visited_complete : found_dist.isNone → VisitedCompleteQueue visited (sx, sy) queue
      invariant found_correct : ∀ d, found_dist = some d → IsShortestDistance (sx, sy) (tx, ty) d
      invariant closed : found_dist.isNone → ClosedSet visited queue
      invariant queue_bound : ∀ x y k, (x, y, k) ∈ queue → ∀ hx hy hd, queue.head? = some (hx, hy, hd) → k ≤ hd + 1
    do
      let (cx, cy, d) := queue.head!
      queue := queue.tail!

      if cx = tx ∧ cy = ty then
        found_dist := some d
      else
        let mut moves_rem := knightMoves
        while !moves_rem.isEmpty
          invariant all_valid_move : AllValidPaths queue (sx, sy)
          invariant queue_shortest_move : QueueShortest queue (sx, sy)
          invariant sorted_move : IsSorted queue
          invariant visited_complete_move : VisitedComplete visited (sx, sy) d
          invariant valid_current : ValidPath (sx, sy) (cx, cy) d
          invariant valid_moves : ∀ dx dy, (dx, dy) ∈ moves_rem → (dx, dy) ∈ knightMoves
          invariant dist_bounds : ∀ x y k, (x, y, k) ∈ queue → d ≤ k ∧ k ≤ d + 1
          invariant closed_move : ∀ x y, (x, y) ∈ visited →
            (∃ d, (x, y, d) ∈ queue) ∨
            ((cx, cy) = (x, y) ∧ ∀ nx ny, (nx - x, ny - y) ∈ knightMoves → (nx - x, ny - y) ∉ moves_rem → (nx, ny) ∈ visited) ∨
            ((cx, cy) ≠ (x, y) ∧ ∀ nx ny, (nx - x, ny - y) ∈ knightMoves → (nx, ny) ∈ visited)
        do
          let (dx, dy) := moves_rem.head!
          moves_rem := moves_rem.tail!

          let nx := cx + dx
          let ny := cy + dy

          if ¬ visited.contains (nx, ny) then
            visited := (nx, ny) :: visited
            queue := queue ++ [(nx, ny, d + 1)]

    return found_dist

prove_correct min_knight_moves by
  loom_goals_intro
  loom_named_split
  all_goals loom_prod_split
  all_goals loom_unfold
  all_goals try grind
  -- 29 goals remaining after loom_solve
  -- Naming scheme: .entry (outer loop), .loop_pos (inner if true), .loop_neg (inner if false), .exit (loop exit)

  case queue_shortest.entry =>
    simp at *
    intros x y d h_in d' h_path
    replace h_in : (x, y, d) ∈ queue := by aesop
    exact queue_shortest x y d h_in d' h_path

  case all_valid.entry =>
    simp at *
    intros x y d h_in
    replace h_in : (x, y, d) ∈ queue := by aesop
    exact all_valid x y d h_in

  case sorted.entry =>
    rw [IsSorted]
    cases h_q : queue with
    | nil => aesop
    | cons hd tl =>
      simp only [h_q, IsSorted, List.map_cons] at sorted
      exact sorted.tail

  case found_correct.entry =>
    have h_i_eq_d : i = d := Option.some_injective _ h
    have h_in : (tx, ty, d) ∈ queue := by
      cases h_q : queue with
      | nil => simp [h_q] at h_1
      | cons hd tl =>
        simp [h_q] at h_3
        rw [h_3, h_4, h_5, h_i_eq_d]
        apply List.mem_cons_self
    rw [IsShortestDistance]
    exact ⟨all_valid tx ty d h_in, queue_shortest tx ty d h_in⟩

  case queue_bound.entry =>
    cases h_q : queue with
    | nil => simp [h_q] at h_1
    | cons head tail =>
      -- Simplify h_6 and h using the decomposition
      simp only [h_q, List.tail!_cons] at h_6 h
      -- (x, y, k) is in the full queue
      have h_in_queue : (x, y, k) ∈ queue := by
        rw [h_q]; exact List.mem_cons_of_mem _ h_6
      -- Get head = (i_1, i_2, i) from h_3
      simp only [h_q] at h_3
      -- Get k ≤ i + 1 from queue_bound
      have h_k_bound : k ≤ i + 1 := by
        apply queue_bound x y k h_in_queue i_1 i_2 i
        rw [h_q, h_3]; rfl
      -- Case split on tail to get hd membership
      cases h_tail : tail with
      | nil => simp [h_tail] at h
      | cons hd' tl' =>
        simp only [h_tail, List.head?_cons, Option.some.injEq] at h
        -- h : hd' = (hx, hy, hd)
        -- Show i ≤ hd from sorted
        rw [h_q, IsSorted, List.map_cons, List.chain'_iff_pairwise, List.pairwise_cons] at sorted
        have h_i_le_hd : i ≤ hd := by
          rw [h_3] at sorted
          apply sorted.1 hd
          simp only [List.mem_map, Prod.exists, exists_eq_right]
          rw [h_tail]
          use hx, hy
          rw [← h]
          apply List.mem_cons_self
        omega

  case all_valid_move.loop_pos =>
    -- Goal: AllValidPaths (queue ++ [(nx, ny, d+1)]) (sx, sy)
    -- Previous proof:
    rw [AllValidPaths]
    intros x y d h_in
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h_in
    cases h_in with
    | inl h_in => exact all_valid_move x y d h_in
    | inr h_in =>
      simp only [Prod.mk.injEq] at h_in
      rw [h_in.1, h_in.2.1, h_in.2.2]
      apply ValidPath.step valid_current
      -- Need to show (i_1 + i_4 - i_1, i_2 + i - i_2) ∈ knightMoves
      -- i.e., (i_4, i) ∈ knightMoves
      have h_move : (i_4, i) ∈ moves_rem := by
        cases h_rem : moves_rem with
        | nil => simp [h_rem] at if_pos_1
        | cons hd tl => simp [h_rem] at h; rw [← h]; apply List.mem_cons_self
      have h_in_knight : (i_4, i) ∈ knightMoves := valid_moves i_4 i h_move
      simp only [add_sub_cancel_left]
      exact h_in_knight

  case queue_shortest_move.loop_pos =>
    rw [QueueShortest]
    intros x y d h_in d' h_path
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h_in
    cases h_in with
    | inl h_in => exact queue_shortest_move x y d h_in d' h_path
    | inr h_in =>
      simp only [Prod.mk.injEq] at h_in
      by_cases h_d' : d' ≤ i_3
      · -- If d' ≤ i_3, node should be in visited, but it's not
        have h_not_visited : (i_1 + i_4, i_2 + i) ∉ visited_1 := by
          simp only [List.contains_eq_mem, Bool.not_eq_true, decide_eq_false_iff_not] at if_pos
          exact if_pos
        rw [h_in.1, h_in.2.1] at h_path
        have h_in_visited := visited_complete_move (i_1 + i_4) (i_2 + i) d' h_path h_d'
        exact absurd h_in_visited h_not_visited
      · push_neg at h_d'; omega

  case sorted_move.loop_pos =>
    -- Goal: IsSorted (queue ++ [(nx, ny, d+1)])
    rw [IsSorted]
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [List.chain'_append]
    constructor
    · rw [IsSorted] at sorted_move; exact sorted_move
    · simp only [List.chain'_singleton, List.getLast?_map, Option.mem_def, Option.map_eq_some_iff,
        Prod.exists, exists_eq_right, List.head?_cons, Option.some.injEq, forall_eq',
        forall_exists_index, true_and]
      intros d_last x y h_last
      have h_in : (x, y, d_last) ∈ queue_1 := by
        rw [List.getLast?_eq_some_iff] at h_last
        obtain ⟨ys, h_eq⟩ := h_last
        rw [h_eq]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      have := dist_bounds x y d_last h_in
      exact this.2

  case visited_complete_move.loop_pos =>
    rw [VisitedComplete]
    intros x y k h_path h_le
    simp only [List.mem_cons]
    right
    exact visited_complete_move x y k h_path h_le

  case valid_moves.loop_pos =>
    apply valid_moves
    cases h_rem : moves_rem with
    | nil => simp [h_rem] at if_pos_1
    | cons hd tl =>
      simp only [h_rem, List.tail!_cons] at h
      exact List.mem_cons_of_mem _ h

  case closed_move.loop_pos =>
    simp only [List.mem_cons] at h
    cases h with
    | inl h_new =>
      -- (x, y) is the new node (i_1 + i_4, i_2 + i)
      left
      use i_3 + 1
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      right
      simp only [Prod.mk.injEq, and_true] at h_new ⊢
      exact ⟨h_new.1, h_new.2⟩
    | inr h_old =>
      -- (x, y) is in old visited
      rcases closed_move x y h_old with h_in_q | ⟨h_eq, h_neighbors⟩ | ⟨h_neq, h_neighbors⟩
      · -- Was in queue → still in queue (append preserves membership)
        left
        rcases h_in_q with ⟨d, h_in⟩
        use d
        simp only [List.mem_append]
        left; exact h_in
      · -- Is the current node (i_1, i_2)
        right; left
        constructor
        · exact h_eq
        · intros nx ny h_move h_not_in_tail
          simp only [List.mem_cons]
          by_cases h_current : (nx - x, ny - y) = (i_4, i)
          · -- This is the current move → neighbor is the new node
            left
            simp only [Prod.mk.injEq] at h_eq h_current ⊢
            constructor <;> omega
          · -- Previously processed move → in old visited
            right
            apply h_neighbors nx ny h_move
            cases h_rem : moves_rem with
            | nil => simp [h_rem] at if_pos_1
            | cons hd tl =>
              simp only [h_rem] at h_4
              rw [List.mem_cons]
              push_neg
              constructor
              · intro h_eq_move; rw [h_4] at h_eq_move; exact h_current h_eq_move
              · intro h_in_tl; apply h_not_in_tail; rw [h_rem, List.tail!_cons]; exact h_in_tl
      · -- Different fully processed node
        right; right
        constructor
        · exact h_neq
        · intros nx ny h_move
          simp only [List.mem_cons]
          right
          exact h_neighbors nx ny h_move


  case valid_moves.loop_neg =>
    cases moves_rem with
    | nil => simp at if_pos
    | cons head tail => aesop

  case closed_move.loop_neg =>
    -- Goal: ClosedMove property (no changes to queue/visited)
    -- Previous proof:
    rcases closed_move x y h with h_in_q | ⟨h_eq, h_neighbors⟩ | ⟨h_neq, h_neighbors⟩
    · -- Was in queue → still in queue (queue unchanged)
      left; exact h_in_q
    · -- Is the current node (i_1, i_2)
      right; left
      constructor
      · exact h_eq
      · intros nx ny h_move h_not_in_tail
        by_cases h_current : (nx - x, ny - y) = (i_4, i)
        · -- This is the current move → neighbor is already in visited (that's why if_neg)
          simp only [Decidable.not_not, List.contains_eq_mem, decide_eq_true_eq] at if_neg
          simp only [Prod.mk.injEq] at h_eq h_current
          convert if_neg using 1
          simp only [Prod.mk.injEq]
          rw [h_eq.1, h_eq.2, ← h_current.1, ← h_current.2]
          simp only [add_sub_cancel, and_self]
        · -- Previously processed move → was already in visited
          apply h_neighbors nx ny h_move
          cases h_rem : moves_rem with
          | nil => simp [h_rem] at if_pos
          | cons hd tl =>
            simp only [h_rem] at h_4
            rw [List.mem_cons]
            push_neg
            constructor
            · intro h_eq_move; rw [h_4] at h_eq_move; exact h_current h_eq_move
            · intro h_in_tl; apply h_not_in_tail; rw [h_rem, List.tail!_cons]; exact h_in_tl
    · -- Different fully processed node
      right
      right
      exact ⟨h_neq, h_neighbors⟩

  case all_valid_move.exit =>
    intros x y d h_in
    apply all_valid
    cases h_q : queue with
    | nil => simp [h_q] at h_1
    | cons hd tl => simp [h_q] at h_in ⊢; aesop

  case queue_shortest_move.exit =>
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff, ne_eq,
      Option.isNone_iff_eq_none, Std.DHashMap.Internal.AssocList.panicWithPosWithDecl_eq,
      not_and] at *
    intros x y d h_in d' h_path
    have h_in_parent : (x, y, d) ∈ queue := by aesop
    exact queue_shortest x y d h_in_parent d' h_path

  case sorted_move.exit =>
    rw [IsSorted, List.chain'_iff_pairwise]
    cases h_q : queue with
    | nil => simp [h_q] at h_1
    | cons hd tl =>
      rw [h_q, IsSorted] at sorted
      simp only [List.map_cons, List.chain'_iff_pairwise, List.pairwise_cons] at sorted
      exact sorted.2

  case visited_complete_move.exit =>
    aesop

  case valid_current.exit =>
    apply all_valid
    cases h_q : queue with
    | nil => simp [h_q] at h_1
    | cons hd tl => aesop

  case dist_bounds.exit.left =>
    -- Goal: d ≤ k (where d is head distance, k is element distance)
    -- Previous proof:
    cases h_q : queue with
    | nil => simp [h_q] at h_1
    | cons hd tl =>
      simp only [h_q, List.tail!_cons] at h
      simp only [h_q] at h_3
      rw [h_q, IsSorted, List.map_cons, List.chain'_iff_pairwise, List.pairwise_cons] at sorted
      have h_hd : hd = (i_1, i_2, i) := h_3
      rw [h_hd] at sorted
      apply sorted.1 k
      simp only [List.mem_map, Prod.exists, exists_eq_right]
      exact ⟨x, y, h⟩

  case dist_bounds.exit.right =>
    cases h_q : queue with
    | nil => simp [h_q] at h_1
    | cons hd tl =>
      simp only [h_q, List.tail!_cons] at h
      have h_in_queue : (x, y, k) ∈ queue := by
        rw [h_q]; exact List.mem_cons_of_mem _ h
      simp only [h_q] at h_3
      apply queue_bound x y k h_in_queue i_1 i_2 i
      rw [h_q, h_3, List.head?_cons]


  case closed_move.exit =>
    have h_closed := closed h_2 x y h
    rcases h_closed with ⟨d, h_in_q⟩ | h_neighbors
    · -- Case A: (x, y) was in queue
      cases h_q : queue with
      | nil => simp [h_q] at h_1
      | cons hd tl =>
        rw [h_q] at h_in_q
        simp only [List.mem_cons] at h_in_q
        cases h_in_q with
        | inl h_head =>
          -- Sub-case A1: (x,y) was the head → middle disjunct
          right; left
          simp only [h_q] at h_3
          simp only [Prod.eq_iff_fst_eq_snd_eq] at h_3 h_head ⊢
          constructor
          · aesop
          · intros nx ny h_move h_not_in; exact absurd h_move h_not_in
        | inr h_tail =>
          -- Sub-case A2: (x,y) was in tail → first disjunct
          left
          simp only [List.tail!_cons]
          exact ⟨d, h_tail⟩
    · -- Case B: All neighbors of (x,y) are in visited
      by_cases h_eq : (i_1, i_2) = (x, y)
      · -- Sub-case B1: (x,y) is the head → middle disjunct (vacuously true)
        right; left
        constructor
        · exact h_eq
        · intros nx ny h_move h_not_in; exact absurd h_move h_not_in
      · -- Sub-case B2: (x,y) ≠ head → third disjunct
        right; right
        exact ⟨h_eq, h_neighbors⟩

  case visited_complete.entry =>
    -- Goal: VisitedCompleteQueue visited (sx, sy) queue
    -- This is the complex proof with ClosedSet reasoning
    -- Previous proof: (very long - see visited_complete.exit in Previous)
    simp [VisitedCompleteQueue]
    split
    · trivial
      -- Get visited = visited_2
    · rename_i a b d q fst
      have h_visited : visited = visited_2 := by simp [h_4.2]
      have h_queue_eq : queue_1 = (b, d, q) :: fst := by simp [h_4.2]

      -- Get bounds on q
      have h_q_bounds : i_3 ≤ q ∧ q ≤ i_3 + 1 := by
        apply dist_bounds b d q
        rw [h_queue_eq]
        apply List.mem_cons_self

      rw [VisitedComplete]
      intros x y k h_path h_le

      -- Case 1: k ≤ i_3
      by_cases h_k : k ≤ i_3
      · rw [h_visited]
        exact visited_complete_move x y k h_path h_k
      · -- Case 2: k > i_3, so k = i_3 + 1 (since k ≤ q ≤ i_3 + 1)
        have h_k_eq : k = i_3 + 1 := by omega
        -- moves_rem is empty
        have h_empty : moves_rem = [] := by
          simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff, ne_eq,
            not_not] at done_1
          cases moves_rem with
          | nil => rfl
          | cons hd tl => simp at done_1
        -- Establish ClosedSet
        have h_closed : ClosedSet visited_2 queue_1 := by
          rw [ClosedSet]
          intros x y h_in
          rcases closed_move x y h_in with h_in_q | ⟨h_eq, h_neighbors⟩ | ⟨h_neq, h_neighbors⟩
          · left; exact h_in_q
          · right; intros nx ny h_move
            apply h_neighbors nx ny h_move
            rw [h_empty]; simp
          · right; exact h_neighbors
        -- Use ClosedSet reasoning for paths of length i_3 + 1
        rw [h_k_eq] at h_path
        obtain ⟨p1, h_path_prev, h_move⟩ : ∃ p1, ValidPath (sx, sy) p1 i_3 ∧ (x - p1.1, y - p1.2) ∈ knightMoves := by
          cases h_path with
          | step h_prev h_mv => exact ⟨_, h_prev, h_mv⟩
        have h_p1_visited : p1 ∈ visited_2 := visited_complete_move p1.1 p1.2 i_3 h_path_prev (Nat.le_refl _)
        have h_p1_closed := h_closed p1.1 p1.2 h_p1_visited
        rcases h_p1_closed with ⟨d', h_in_q⟩ | h_neighbors
        · have h_d_ge : i_3 ≤ d' := (dist_bounds p1.1 p1.2 d' h_in_q).1
          have h_shortest := queue_shortest_move p1.1 p1.2 d' h_in_q i_3 h_path_prev
          have h_d_eq : d' = i_3 := by omega
          rw [h_queue_eq, IsSorted, List.map_cons, List.chain'_iff_pairwise, List.pairwise_cons] at sorted_move
          have h_q_le_d' : q ≤ d' := by
            by_cases h_q : q = i_3
            · omega
            · -- q ≠ i_3, so q = i_3 + 1 (from h_q_bounds)
              have h_q_eq : q = i_3 + 1 := by omega
              -- But (p1.1, p1.2, d') ∈ queue with d' = i_3
              -- Head has distance q = i_3 + 1 > i_3 = d'
              -- This contradicts sorted: head should be ≤ all elements
              rw [h_queue_eq] at h_in_q
              simp only [List.mem_cons] at h_in_q
              cases h_in_q with
              | inl h_head =>
                -- (p1.1, p1.2, d') is the head (b, d, q)
                simp only [Prod.mk.injEq] at h_head
                omega  -- d' = q but d' = i_3 and q = i_3 + 1
              | inr h_tail =>
                -- (p1.1, p1.2, d') is in tail with d' = i_3 < i_3 + 1 = q
                -- But sorted says head ≤ all tail elements: q ≤ d'
                have h_sorted := sorted_move.1 d' (by simp [List.mem_map]; exact ⟨p1.1, p1.2, h_tail⟩)
                omega  -- q ≤ d' but q = i_3 + 1 and d' = i_3
          omega
        · rw [h_visited]
          exact h_neighbors x y h_move

  case closed.entry =>
    rw [ClosedSet]
    intros x y h_in
    -- Get that visited = visited_2 and i = queue_1
    have h_visited : visited = visited_2 := by simp [h_4.2]
    have h_queue : i = queue_1 := by simp [h_4.2]
    rw [h_visited] at h_in
    rw [h_queue]
    -- moves_rem is empty
    have h_empty : moves_rem = [] := by
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff, ne_eq,
        not_not] at done_1
      cases moves_rem with
      | nil => rfl
      | cons hd tl => simp at done_1
    rcases closed_move x y h_in with h_in_q | ⟨h_eq, h_neighbors⟩ | ⟨h_neq, h_neighbors⟩
    · -- Was in queue
      left; exact h_in_q
    · -- Is current node - all neighbors are in visited since moves_rem is empty
      right
      intros nx ny h_move
      rw [h_visited]
      apply h_neighbors nx ny h_move
      rw [h_empty]
      simp
    · -- Different fully processed node
      right
      convert h_neighbors



  case queue_bound.entry =>
    -- Get that i = queue_1
    have h_queue : i = queue_1 := by simp [h_4.2]
    -- k ≤ i_3 + 1 from dist_bounds
    have h_k_bound : k ≤ i_3 + 1 := by
      rw [h_queue] at h_5
      exact (dist_bounds x y k h_5).2
    have h_head_in : (hx, hy, hd) ∈ queue_1 := by
      cases h_q : queue_1 with
      | nil => simp [h_queue, h_q] at h
      | cons hd' tl =>
        rw [h_queue, h_q, List.head?_cons] at h
        simp at h
        rw [← h]
        apply List.mem_cons_self
    -- i_3 ≤ hd from dist_bounds applied to head
    have h_hd_bound : i_3 ≤ hd := (dist_bounds hx hy hd h_head_in).1
    omega

  case all_valid.entry =>
    intros x y d h_in
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h_in
    rw [h_in.1, h_in.2.1, h_in.2.2]
    exact ValidPath.zero

  case queue_shortest.entry =>
    intros x y d h_in d' h_path
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h_in
    rw [h_in.2.2]
    exact Nat.zero_le _

  case sorted.entry =>
    rw [IsSorted]
    aesop

  case visited_complete.entry =>
    rw [VisitedCompleteQueue, VisitedComplete]
    intros x y k h_path h_le
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
    replace h_le : k = 0 := by grind
    rw [h_le] at h_path
    cases h_path
    aesop

  case closed.entry =>
    rw [ClosedSet]
    aesop


#print axioms min_knight_moves_correct

#guard (min_knight_moves 0 0 1 2).extract == some 1
#guard (min_knight_moves 0 0 3 3).extract == some 2
#guard (min_knight_moves 0 0 4 5).extract == some 3
#guard (min_knight_moves 0 0 5 5).extract == some 4
#guard (min_knight_moves 0 0 0 0).extract == some 0

def benchmark_bfs (ns : List Nat) : IO Unit := do
  IO.println "Starting BFS Benchmark..."
  let mut results : List (Nat × Nat) := []
  for n in ns do
    let start ← IO.getNumHeartbeats
    let res := (min_knight_moves 0 0 (n : Int) (n : Int)).extract
    -- Force evaluation of the pure value
    let _ := toString res
    let stop ← IO.getNumHeartbeats
    let hb := stop - start
    IO.println s!"Target: ({n}, {n}) | Result: {res} | Heartbeats: {hb}"
    results := results ++ [(n, hb)]

  IO.println "\nHeartbeats Graph:"
  let max_hb := results.foldl (fun m (_, hb) => Nat.max m hb) 0
  let width := 50
  for (n, hb) in results do
    let bar_len := if max_hb == 0 then 0 else (hb * width) / max_hb
    let bar := String.mk (List.replicate bar_len '#')
    IO.println s!"{n} | {bar} {hb}"

-- Run benchmark for diagonal targets from (10,10) to (50, 50)
#eval benchmark_bfs [10, 20, 30, 40, 50]
