import Auto

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
set_option maxHeartbeats 10000000

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
  loom_solve
  -- extract_goal
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
  case all_valid.entry_1 =>
    intros x y d h_in
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h_in
    rw [h_in.1, h_in.2.1, h_in.2.2]
    exact ValidPath.zero
  case all_valid_move.loop =>
    simp at *
    intros x y d_1 h_in
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h_in
    cases h_in with
    | inl h_in => exact all_valid_move x y d_1 h_in
    | inr h_in =>
      simp only [Prod.mk.injEq] at h_in
      rw [h_in.1, h_in.2.1, h_in.2.2]
      apply ValidPath.step
      · exact valid_current
      · grind

  case queue_shortest_move.loop =>
    simp at *
    intros x y d h_in d' h_path
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h_in
    cases h_in with
    | inl h_in => exact queue_shortest_move x y d h_in d' h_path
    | inr h_in =>
      contrapose! visited_complete_move
      rw [VisitedComplete]
      push_neg
      use x, y, d'
      constructor
      · exact h_path
      · simp only [Prod.mk.injEq] at h_in
        constructor
        · grind
        · convert if_pos_1 <;> grind
  case queue_shortest_move.exit_1 =>
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff, ne_eq,
      Option.isNone_iff_eq_none, Std.DHashMap.Internal.AssocList.panicWithPosWithDecl_eq,
      not_and] at *
    intros x y d h_in d' h_path
    have h_in_parent : (x, y, d) ∈ queue := by aesop
    exact queue_shortest x y d h_in_parent d' h_path
  case queue_shortest.entry_1 =>
    intros x y d h_in d' h_path
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h_in
    rw [h_in.2.2]
    exact Nat.zero_le _
  case visited_complete.entry_1 =>
    rw [VisitedCompleteQueue, VisitedComplete]
    intros x y k h_path h_le
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
    replace h_le : k = 0 := by grind
    rw [h_le] at h_path
    cases h_path
    aesop
  case visited_complete_move.loop =>
    intros x y k h_path h_le
    -- We know it's in the old visited set
    have h_in_old := visited_complete_move x y k h_path h_le
    -- Therefore it's in the new visited set (which is just old + one new element)
    simp [List.mem_cons]
    right
    exact h_in_old
  case found_correct.entry =>
    have h_in : (tx, ty, d) ∈ queue := by
      rw [←a_2, ←a_3, ←(Option.some_inj.1 a_4)]
      cases queue <;> simp_all
    exact all_valid tx ty d h_in
  case found_correct.entry_1 =>
    have h_in : (tx, ty, d) ∈ queue := by
      rw [←a_2, ←a_3, ←(Option.some_inj.1 a_4)]
      cases queue <;> simp_all

    exact queue_shortest tx ty d h_in d' a_5
  case visited_complete_move.exit_1 => aesop
  case visited_complete.exit =>
    simp [VisitedCompleteQueue]
    split
    · trivial
    · rename_i hx hy hd tail
      -- Goal: VisitedComplete visited_1 (sx, sy) hd
      have h_v : visited_1 = visited_2 := by simp at i_6 <;> aesop
      -- 1. Establish ClosedSet for the current state
      have h_closed : ClosedSet visited_1 queue_1 := by
        -- Follows from closed_move and the fact that moves_rem is empty

        have h_empty : moves_rem = [] := by
          simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff, ne_eq,
            not_not] at done_2
          exact done_2
        rw [ClosedSet]
        intros x y h_in
        have h_closed_move := closed_move x y h_in
        cases h_closed_move with
        | inl h_in_q =>
          rcases h_in_q with ⟨d, hd⟩
          left
          use d
        | inr h_cases =>
          right
          cases h_cases with
          | inl h_eq =>
            intros nx ny h_move
            apply h_eq.2 nx ny h_move
            rw [h_empty]
            aesop
          | inr h_neq =>
            intros nx ny h_move
            exact h_neq.2 nx ny h_move

        -- 2. Establish bounds on hd (the distance of the next node in queue)
      have h_hd_bounds : i_2 ≤ hd ∧ hd ≤ i_2 + 1 := by
          -- Follows from dist_bounds applied to the head of queue_1
          apply dist_bounds hx hy hd
          simp only [MProdWithNames.mk.injEq] at i_6
          rw [i_6.2.1]
          simp only [List.mem_cons, true_or]

      -- 3. Main logic: Prove VisitedComplete for the new limit hd
      intros x y k h_path h_le
      rcases h_hd_bounds with ⟨h_ge, h_le_hd⟩

      -- Case 1: k is within the old limit i_2
      by_cases h_k: k ≤ i_2
      · convert visited_complete_move x y k h_path h_k
        aesop
      · have h_k_ge : i_2 + 1 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_not_le h_k)
        have h_k_eq : k = i_2 + 1 := by
          apply Nat.le_antisymm
          · exact le_trans h_le h_le_hd
          · exact h_k_ge
        cases h_path with
        | zero =>
          simp only [Option.isNone_iff_eq_none, Bool.not_eq_eq_eq_not, Bool.not_true,
            List.isEmpty_eq_false_iff, ne_eq,
            Std.DHashMap.Internal.AssocList.panicWithPosWithDecl_eq, not_and, Prod.mk.injEq,
            not_not, MProdWithNames.mk.injEq, zero_le, not_true_eq_false] at *
        | step h_path_p h_move =>
          rename_i p1 p2
          have h_p_in_visited : p1 ∈ visited_1 := by
            have h_i_2_eq : i_2 = p2 := by
              grind
            rw [← h_i_2_eq] at h_path_p
            exact visited_complete_move _ _ i_2 h_path_p (Nat.le_refl _)
          have h_p_not_in_queue : ∀ d, (p1.1, p1.2, d) ∉ queue_1 := by
            intro d h_in
            have h_d_bounds := dist_bounds p1.1 p1.2 d h_in
            have h_shortest := queue_shortest_move p1.1 p1.2 d h_in p2 h_path_p
            have h_p2_eq : p2 = i_2 := by aesop
            have h_d_eq : d = i_2 := by aesop

            -- 2. Establish that hd = i_2 + 1
            -- We know p2 + 1 ≤ hd (from h_le) and p2 = i_2
            have h_hd_ge : i_2 + 1 ≤ hd := by aesop
            -- We also know hd ≤ i_2 + 1 from dist_bounds on the head (h_le_hd)
            have h_hd_eq : hd = i_2 + 1 := by aesop

            -- 3. Contradiction: The queue is sorted, so head distance (hd) must be ≤ any element distance (d)
            -- Note: This relies on IsSorted. If IsSorted is missing from context, it needs to be added back.
            have h_sorted_head : hd ≤ d := by
              -- If IsSorted is available:
              simp only [MProdWithNames.mk.injEq] at i_6
              rw [i_6.2.1] at sorted_move h_in
              simp only [IsSorted, List.chain'_iff_pairwise, List.map_cons, List.pairwise_cons] at sorted_move
              rcases h_in with ⟨rfl, rfl, rfl⟩ | h_in
              · exact Nat.le_refl _
              · grind
              · apply sorted_move.1
                simp only [List.mem_map]
                use (p1.1, p1.2, d)
                constructor
                · aesop
                · rw [h_d_eq]
            rw [h_d_eq, h_hd_eq] at h_sorted_head
            aesop
          have h_p_closed := h_closed p1.1 p1.2 h_p_in_visited
          cases h_p_closed with
          | inl h_in_q =>
            exfalso
            rcases h_in_q with ⟨d, h_in⟩
            exact h_p_not_in_queue d h_in
            | inr h_neighbors =>
            -- Therefore (x, y) is in visited
          rw [← h_v]
          apply h_neighbors x y h_move
  case found_correct.exit_2 =>
    apply (found_correct d a).1
  case found_correct.exit_3 =>
    apply (found_correct d a).2 d' a_1
  case valid_moves.loop =>
    apply valid_moves
    cases moves_rem with
    | nil => simp at if_pos
    | cons head tail =>
      simp only [List.tail!_cons] at a_2
      aesop
  case valid_moves.loop_1 =>
    apply valid_moves
    cases moves_rem with
    | nil => simp at if_pos
    | cons head tail =>
      simp only [List.tail!_cons] at a_2
      aesop
  case all_valid_move.exit_1 =>
    intros x y d h_in
    apply all_valid
    cases queue <;> simp_all [List.mem_cons]
  case valid_current.exit_1 =>
    apply all_valid
    cases queue <;> simp_all [List.mem_cons]

  case queue_bound.entry =>
    have h_q : queue = (i, i_1, i_2) :: queue.tail! := by
      cases queue <;> simp_all

    -- 2. Get k ≤ i_2 + 1 from old invariant
    have h_k_bound : k ≤ i_2 + 1 := by
      apply queue_bound x y k
      · rw [h_q]; simp [List.mem_cons]; right; exact a_4
      · rw [h_q]; rfl

    -- 3. Get i_2 ≤ hd from sorted
    have h_i2_le_hd : i_2 ≤ hd := by
      have := sorted
      rw [h_q, IsSorted] at this
      simp only [List.map_cons, List.chain'_iff_pairwise, List.pairwise_cons] at this
      apply this.1 hd
      simp only [List.mem_map, Prod.exists, exists_eq_right]
      use hx, hy
      replace a_5 := List.head_of_head?_eq_some a_5
      grind
    grind
  case dist_bounds.exit_2 =>
    cases h_q : queue with
    | nil => aesop -- Contradiction: queue cannot be empty
    | cons head tail =>
      -- 2. Align our variables with the decomposition
      simp [h_q] at i_3
      simp [h_q] at a_2 -- a_2 becomes (x, y, k) ∈ tail

      -- 3. Use the sorted property
      rw [h_q, IsSorted] at sorted
      -- Convert Chain' to Pairwise because ≤ is transitive
      simp only [List.map_cons, List.chain'_iff_pairwise, List.pairwise_cons, List.mem_map,
        Prod.exists, exists_eq_right, forall_exists_index, i_3] at sorted

      -- sorted.1 says: ∀ d ∈ tail.map distance, head.distance ≤ d
      exact sorted.1 k x y a_2
  case dist_bounds.exit_3 =>
    cases h_q : queue with
    | nil => aesop -- Impossible case
    | cons head tail =>
      simp [h_q] at i_3
      simp [h_q] at a_2 -- a_2 is in tail
      -- 2. Apply queue_bound
      apply queue_bound x y k
      · rw [h_q]; simp [List.mem_cons]; right; exact a_2
      · aesop
  case sorted.entry =>
    rw [IsSorted]
    cases queue <;> simp_all [List.chain'_iff_pairwise]
    case cons head tail =>
      rw [IsSorted] at sorted
      simp only [List.map_cons, List.chain'_iff_pairwise, List.pairwise_cons] at sorted
      exact sorted.2
  case sorted_move.loop =>
    rw [IsSorted]
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [List.chain'_append]
    constructor
    · exact sorted_move
    · simp only [List.chain'_singleton, List.getLast?_map, Option.mem_def, Option.map_eq_some_iff,
      Prod.exists, exists_eq_right, List.head?_cons, Option.some.injEq, forall_eq',
      forall_exists_index, true_and]
      intros d_last x y h_last
      have h_in : (x, y, d_last) ∈ queue_1 := by
        rw [List.getLast?_eq_some_iff] at h_last
        grind
      have := dist_bounds x y d_last h_in
      exact this.2

  case sorted_move.exit_1 =>
    rw [IsSorted, List.chain'_iff_pairwise]
    cases h_q : queue with
    | nil => simp [h_q] at a
    | cons head tail =>
      rw [h_q, IsSorted] at sorted
      simp only [List.map_cons, List.chain'_iff_pairwise, List.pairwise_cons] at sorted
      exact sorted.2
  case sorted.entry_1 =>
    rw [IsSorted]
    aesop
  case queue_bound.exit =>
    simp at i_6
    rw [← i_6.2.1] at a_2 a_3
    have h_in : (x, y, k) ∈ queue_1 := a_2
    have h_head : queue_1.head? = some (hx, hy, hd) := a_3

    -- We know from dist_bounds that every element in queue_1 has distance ≤ i_2 + 1
    have h_k_bound : k ≤ i_2 + 1 := (dist_bounds x y k h_in).2

    -- We also know from dist_bounds that the head element has distance ≥ i_2
    have h_head_in : (hx, hy, hd) ∈ queue_1 := by
      cases h_q : queue_1 with
      | nil => simp [h_q] at h_head
      | cons h t =>
        rw [h_q] at h_head
        simp at h_head
        rw [← h_head]
        apply List.mem_cons_self

    have h_hd_bound : i_2 ≤ hd := (dist_bounds hx hy hd h_head_in).1
    grind
  case closed_move.loop_1 =>
      simp at a_2 ⊢
      rcases closed_move x y a_2 with h_in_q | ⟨h_eq, h_neighbors⟩ | ⟨h_neq, h_neighbors⟩
      · -- Case 1: Node is still in queue
        left; exact h_in_q
      · -- Case 2: Node is the current one being expanded
        right; left
        constructor
        · aesop
        · intros nx ny h_move h_not_in_tail
          -- Check if this is the move we just processed or an older one
          by_cases h_current : (nx - x, ny - y) = (i_4, i_5)
          · -- Subcase 2a: It is the current move (i_4, i_5)
            -- We know it is visited because if_neg_1 says contains is true
            simp only [List.contains_eq_mem, decide_eq_true_eq, Decidable.not_not] at if_neg_1
            convert if_neg_1 <;> aesop
          · -- Subcase 2b: It is a previously processed move
            apply h_neighbors nx ny h_move
            -- Logic: Not in tail AND not current head => Not in list
            cases h_rem : moves_rem with
            | nil => simp [h_rem] at if_pos
            | cons h t =>
              simp [h_rem] at i_6
              rw [List.mem_cons]
              push_neg
              constructor
              · grind
              · contrapose! h_not_in_tail
                rw [h_rem, List.tail!_cons]
                exact h_not_in_tail

      · -- Case 3: Node is a different, fully processed node
        right; right; aesop
  case closed_move.loop =>
    simp at a_2 ⊢
    cases a_2 with
    | inl h_new =>
      -- Case 1: (x, y) is the newly visited node
      left
      use i_2 + 1
      grind
    | inr h_old =>
      -- Case 2: (x, y) is an old visited node
      rcases closed_move x y h_old with h_in_q | ⟨h_eq, h_neighbors⟩ | ⟨h_neq, h_neighbors⟩
      · -- Subcase 2a: It was already in the queue
        left
        rcases h_in_q with ⟨d, h_in⟩
        use d
        simp [h_in]
      · -- Subcase 2b: It is the current node (i, i_1)
        right; left
        constructor
        · aesop
        · intros nx ny h_move h_not_in_tail
          -- Check if move is the current one or older
          by_cases h_current : (nx - x, ny - y) = (i_4, i_5)
          · -- It is the current move -> neighbor is the new node
            simp only [Std.DHashMap.Internal.AssocList.panicWithPosWithDecl_eq] at i_6
            have : nx = i + i_4 ∧ ny = i_1 + i_5 := by aesop
            rw [this.1, this.2]
            left; grind
          · -- It is an older move -> neighbor in old visited
            right
            apply h_neighbors nx ny h_move
            -- Logic to show it's not in moves_rem
            cases h_rem : moves_rem with
            | nil => simp [h_rem] at if_pos
            | cons h t =>
              simp [h_rem] at i_6
              rw [List.mem_cons]
              push_neg
              constructor
              · grind
              · contrapose! h_not_in_tail
                rw [h_rem, List.tail!_cons]
                exact h_not_in_tail
      · -- Subcase 2c: It is another fully processed node
        right; right
        constructor
        · aesop
        · intros nx ny h_move
          right
          exact h_neighbors nx ny h_move
  case closed_move.exit_1 =>
    simp at a_2 ⊢
    have h_closed_old := closed a_1 x y a_2
    rcases h_closed_old with ⟨d, h_in_q⟩ | h_neighbors
    · cases h_q : queue with
      | nil => simp [h_q] at a
      | cons head tail =>
        rw [h_q] at h_in_q
        simp at h_in_q
        cases h_in_q with
        | inl h_head =>
          -- It was the head
          simp only [h_q] at i_3
          simp only [List.tail!_cons]
          grind
        | inr h_tail =>
          aesop
    · grind
  case closed.exit =>
    rw [ClosedSet]
    intros x y h_in
    simp only [MProdWithNames.mk.injEq] at i_6
    rw [← i_6.2.2, ← i_6.2.1]
    rw [← i_6.2.2] at h_in
    have := closed_move x y h_in
    rcases this with h_in_q | ⟨h_eq, h_neighbors⟩ | ⟨h_neq, h_neighbors⟩
    · -- Case 1: In queue
      left; exact h_in_q
    · -- Case 2: Current node
      right
      intros nx ny h_move
      apply h_neighbors nx ny h_move
      -- Since moves_rem is empty, any move is NOT in moves_rem
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff, ne_eq, not_not] at done_2
      rw [done_2]
      aesop
    · -- Case 3: Other node
      right; exact h_neighbors
  case closed.entry_1 =>
    rw [ClosedSet]
    aesop


#print axioms min_knight_moves_correct

#guard (min_knight_moves 0 0 1 2).extract == some 1
#guard (min_knight_moves 0 0 3 3).extract == some 2
#guard (min_knight_moves 0 0 4 5).extract == some 3
#guard (min_knight_moves 0 0 5 5).extract == some 4
#guard (min_knight_moves 0 0 0 0).extract == some 0
#eval min_knight_moves 0 0 10 10
