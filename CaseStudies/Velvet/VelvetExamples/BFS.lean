import Auto

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
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
  loom_solve
  -- 29 goals remaining after loom_solve
  -- Naming scheme: .entry (outer loop), .loop_pos (inner if true), .loop_neg (inner if false), .exit (loop exit)

  case queue_shortest.entry =>
    -- Goal: QueueShortest queue.tail! (sx, sy)
    -- Previous proof:
    -- simp at *
    -- intros x y d h_in d' h_path
    -- replace h_in : (x, y, d) ∈ queue := by aesop
    -- exact queue_shortest x y d h_in d' h_path
    sorry

  case all_valid.entry =>
    -- Goal: AllValidPaths queue.tail! (sx, sy)
    -- Previous proof:
    -- simp at *
    -- intros x y d h_in
    -- replace h_in : (x, y, d) ∈ queue := by aesop
    -- exact all_valid x y d h_in
    sorry

  case sorted.entry =>
    -- Goal: IsSorted queue.tail!
    -- Previous proof:
    -- rw [IsSorted]
    -- cases queue <;> simp_all [List.chain'_iff_pairwise]
    -- case cons head tail =>
    --   rw [IsSorted] at sorted
    --   simp only [List.map_cons, List.chain'_iff_pairwise, List.pairwise_cons] at sorted
    --   exact sorted.2
    sorry

  case found_correct.entry =>
    -- Goal: ValidPath (sx, sy) (tx, ty) d  (first part of IsShortestDistance)
    -- Previous proof:
    -- have h_in : (tx, ty, d) ∈ queue := by
    --   rw [←a_2, ←a_3, ←(Option.some_inj.1 a_4)]
    --   cases queue <;> simp_all
    -- exact all_valid tx ty d h_in
    sorry

  case queue_bound.entry =>
    -- Goal: k ≤ hd + 1
    -- Previous proof:
    -- have h_q : queue = (i, i_1, i_2) :: queue.tail! := by cases queue <;> simp_all
    -- have h_k_bound : k ≤ i_2 + 1 := by
    --   apply queue_bound x y k
    --   · rw [h_q]; simp [List.mem_cons]; right; exact a_4
    --   · rw [h_q]; rfl
    -- have h_i2_le_hd : i_2 ≤ hd := by
    --   have := sorted
    --   rw [h_q, IsSorted] at this
    --   simp only [List.map_cons, List.chain'_iff_pairwise, List.pairwise_cons] at this
    --   apply this.1 hd
    --   simp only [List.mem_map, Prod.exists, exists_eq_right]
    --   use hx, hy
    --   replace a_5 := List.head_of_head?_eq_some a_5
    --   grind
    -- grind
    sorry

  case all_valid_move.loop_pos =>
    -- Goal: AllValidPaths (queue ++ [(nx, ny, d+1)]) (sx, sy)
    -- Previous proof:
    -- simp at *
    -- intros x y d_1 h_in
    -- simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h_in
    -- cases h_in with
    -- | inl h_in => exact all_valid_move x y d_1 h_in
    -- | inr h_in =>
    --   simp only [Prod.mk.injEq] at h_in
    --   rw [h_in.1, h_in.2.1, h_in.2.2]
    --   apply ValidPath.step
    --   · exact valid_current
    --   · grind
    sorry

  case queue_shortest_move.loop_pos =>
    -- Goal: QueueShortest (queue ++ [(nx, ny, d+1)]) (sx, sy)
    -- Previous proof:
    -- simp at *
    -- intros x y d h_in d' h_path
    -- simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h_in
    -- cases h_in with
    -- | inl h_in => exact queue_shortest_move x y d h_in d' h_path
    -- | inr h_in =>
    --   contrapose! visited_complete_move
    --   rw [VisitedComplete]
    --   push_neg
    --   use x, y, d'
    --   constructor
    --   · exact h_path
    --   · simp only [Prod.mk.injEq] at h_in
    --     constructor
    --     · grind
    --     · convert if_pos_1 <;> grind
    sorry

  case sorted_move.loop_pos =>
    -- Goal: IsSorted (queue ++ [(nx, ny, d+1)])
    -- Previous proof:
    -- rw [IsSorted]
    -- simp only [List.map_append, List.map_cons, List.map_nil]
    -- rw [List.chain'_append]
    -- constructor
    -- · exact sorted_move
    -- · simp only [List.chain'_singleton, List.getLast?_map, Option.mem_def, Option.map_eq_some_iff,
    --     Prod.exists, exists_eq_right, List.head?_cons, Option.some.injEq, forall_eq',
    --     forall_exists_index, true_and]
    --   intros d_last x y h_last
    --   have h_in : (x, y, d_last) ∈ queue_1 := by
    --     rw [List.getLast?_eq_some_iff] at h_last
    --     grind
    --   have := dist_bounds x y d_last h_in
    --   exact this.2
    sorry

  case visited_complete_move.loop_pos =>
    -- Goal: VisitedComplete ((nx,ny) :: visited) (sx, sy) d
    -- Previous proof:
    -- intros x y k h_path h_le
    -- have h_in_old := visited_complete_move x y k h_path h_le
    -- simp [List.mem_cons]
    -- right
    -- exact h_in_old
    sorry

  case valid_moves.loop_pos =>
    -- Goal: (dx, dy) ∈ knightMoves
    -- Previous proof:
    -- apply valid_moves
    -- cases moves_rem with
    -- | nil => simp at if_pos
    -- | cons head tail => simp only [List.tail!_cons] at a_2; aesop
    sorry

  case closed_move.loop_pos =>
    -- Goal: ClosedMove property for (x,y) ∈ (new_node :: visited)
    -- Previous proof:
    -- simp at a_2 ⊢
    -- cases a_2 with
    -- | inl h_new =>
    --   left
    --   use i_2 + 1
    --   grind
    -- | inr h_old =>
    --   rcases closed_move x y h_old with h_in_q | ⟨h_eq, h_neighbors⟩ | ⟨h_neq, h_neighbors⟩
    --   · left; rcases h_in_q with ⟨d, h_in⟩; use d; simp [h_in]
    --   · right; left
    --     constructor
    --     · aesop
    --     · intros nx ny h_move h_not_in_tail
    --       by_cases h_current : (nx - x, ny - y) = (i_4, i_5)
    --       · simp only [Std.DHashMap.Internal.AssocList.panicWithPosWithDecl_eq] at i_6
    --         have : nx = i + i_4 ∧ ny = i_1 + i_5 := by aesop
    --         rw [this.1, this.2]
    --         left; grind
    --       · right
    --         apply h_neighbors nx ny h_move
    --         cases h_rem : moves_rem with
    --         | nil => simp [h_rem] at if_pos
    --         | cons h t =>
    --           simp [h_rem] at i_6
    --           rw [List.mem_cons]
    --           push_neg
    --           constructor
    --           · grind
    --           · contrapose! h_not_in_tail; rw [h_rem, List.tail!_cons]; exact h_not_in_tail
    --   · right; right; constructor; · aesop; · intros nx ny h_move; right; exact h_neighbors nx ny h_move
    sorry

  case valid_moves.loop_neg =>
    -- Goal: (dx, dy) ∈ knightMoves
    -- Previous proof:
    -- apply valid_moves
    -- cases moves_rem with
    -- | nil => simp at if_pos
    -- | cons head tail => simp only [List.tail!_cons] at a_2; aesop
    sorry

  case closed_move.loop_neg =>
    -- Goal: ClosedMove property (no changes to queue/visited)
    -- Previous proof:
    -- simp at a_2 ⊢
    -- rcases closed_move x y a_2 with h_in_q | ⟨h_eq, h_neighbors⟩ | ⟨h_neq, h_neighbors⟩
    -- · left; exact h_in_q
    -- · right; left
    --   constructor
    --   · aesop
    --   · intros nx ny h_move h_not_in_tail
    --     by_cases h_current : (nx - x, ny - y) = (i_4, i_5)
    --     · simp only [List.contains_eq_mem, decide_eq_true_eq, Decidable.not_not] at if_neg_1
    --       convert if_neg_1 <;> aesop
    --     · apply h_neighbors nx ny h_move
    --       cases h_rem : moves_rem with
    --       | nil => simp [h_rem] at if_pos
    --       | cons h t =>
    --         simp [h_rem] at i_6
    --         rw [List.mem_cons]
    --         push_neg
    --         constructor
    --         · grind
    --         · contrapose! h_not_in_tail; rw [h_rem, List.tail!_cons]; exact h_not_in_tail
    -- · right; right; aesop
    sorry

  -- ============================================================
  -- INNER LOOP EXIT (moves_rem empty, if_neg: ¬(cx = tx ∧ cy = ty))
  -- ============================================================

  case all_valid_move.exit =>
    -- Goal: AllValidPaths queue.tail! (sx, sy)
    -- Previous proof:
    -- intros x y d h_in
    -- apply all_valid
    -- cases queue <;> simp_all [List.mem_cons]
    sorry

  case queue_shortest_move.exit =>
    -- Goal: QueueShortest queue.tail! (sx, sy)
    -- Previous proof:
    -- simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff, ne_eq,
    --   Option.isNone_iff_eq_none, Std.DHashMap.Internal.AssocList.panicWithPosWithDecl_eq,
    --   not_and] at *
    -- intros x y d h_in d' h_path
    -- have h_in_parent : (x, y, d) ∈ queue := by aesop
    -- exact queue_shortest x y d h_in_parent d' h_path
    sorry

  case sorted_move.exit =>
    -- Goal: IsSorted queue.tail!
    -- Previous proof:
    -- rw [IsSorted, List.chain'_iff_pairwise]
    -- cases h_q : queue with
    -- | nil => simp [h_q] at a
    -- | cons head tail =>
    --   rw [h_q, IsSorted] at sorted
    --   simp only [List.map_cons, List.chain'_iff_pairwise, List.pairwise_cons] at sorted
    --   exact sorted.2
    sorry

  case visited_complete_move.exit =>
    -- Goal: VisitedComplete visited (sx, sy) d
    -- Previous proof: aesop
    sorry

  case valid_current.exit =>
    -- Goal: ValidPath (sx, sy) (cx, cy) d
    -- Previous proof:
    -- apply all_valid
    -- cases queue <;> simp_all [List.mem_cons]
    sorry

  case dist_bounds.exit.left =>
    -- Goal: d ≤ k (where d is head distance, k is element distance)
    -- Previous proof:
    -- cases h_q : queue with
    -- | nil => aesop
    -- | cons head tail =>
    --   simp [h_q] at i_3
    --   simp [h_q] at a_2
    --   rw [h_q, IsSorted] at sorted
    --   simp only [List.map_cons, List.chain'_iff_pairwise, List.pairwise_cons,
    --     List.mem_map, Prod.exists, exists_eq_right, forall_exists_index, i_3] at sorted
    --   exact sorted.1 k x y a_2
    sorry

  case dist_bounds.exit.right =>
    -- Goal: k ≤ d + 1
    -- Previous proof:
    -- cases h_q : queue with
    -- | nil => aesop
    -- | cons head tail =>
    --   simp [h_q] at i_3
    --   simp [h_q] at a_2
    --   apply queue_bound x y k
    --   · rw [h_q]; simp [List.mem_cons]; right; exact a_2
    --   · aesop
    sorry

  case closed_move.exit =>
    -- Goal: ClosedSet for queue.tail!
    -- Previous proof:
    -- simp at a_2 ⊢
    -- have h_closed_old := closed a_1 x y a_2
    -- rcases h_closed_old with ⟨d, h_in_q⟩ | h_neighbors
    -- · cases h_q : queue with
    --   | nil => simp [h_q] at a
    --   | cons head tail =>
    --     rw [h_q] at h_in_q
    --     simp at h_in_q
    --     cases h_in_q with
    --     | inl h_head => simp only [h_q] at i_3; simp only [List.tail!_cons]; grind
    --     | inr h_tail => aesop
    -- · grind
    sorry

  case visited_complete.entry =>
    -- Goal: VisitedCompleteQueue visited (sx, sy) queue
    -- This is the complex proof with ClosedSet reasoning
    -- Previous proof: (very long - see visited_complete.exit in Previous)
    -- simp [VisitedCompleteQueue]
    -- split
    -- · trivial
    -- · rename_i hx hy hd tail
    --   have h_v : visited_1 = visited_2 := by simp at i_6 <;> aesop
    --   have h_closed : ClosedSet visited_1 queue_1 := by ...
    --   have h_hd_bounds : i_2 ≤ hd ∧ hd ≤ i_2 + 1 := by ...
    --   intros x y k h_path h_le
    --   ... (complex case analysis on ValidPath)
    sorry

  case closed.entry =>
    -- Goal: ClosedSet visited queue
    -- Previous proof:
    -- rw [ClosedSet]
    -- intros x y h_in
    -- simp only [MProdWithNames.mk.injEq] at i_6
    -- rw [← i_6.2.2, ← i_6.2.1]
    -- rw [← i_6.2.2] at h_in
    -- have := closed_move x y h_in
    -- rcases this with h_in_q | ⟨h_eq, h_neighbors⟩ | ⟨h_neq, h_neighbors⟩
    -- · left; exact h_in_q
    -- · right
    --   intros nx ny h_move
    --   apply h_neighbors nx ny h_move
    --   simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff, ne_eq, not_not] at done_2
    --   rw [done_2]
    --   aesop
    -- · right; exact h_neighbors
    sorry

  case queue_bound.entry =>
    -- Goal: k ≤ hd + 1 (for outer loop continuation)
    -- Previous proof:
    -- simp at i_6
    -- rw [← i_6.2.1] at a_2 a_3
    -- have h_in : (x, y, k) ∈ queue_1 := a_2
    -- have h_head : queue_1.head? = some (hx, hy, hd) := a_3
    -- have h_k_bound : k ≤ i_2 + 1 := (dist_bounds x y k h_in).2
    -- have h_head_in : (hx, hy, hd) ∈ queue_1 := by
    --   cases h_q : queue_1 with
    --   | nil => simp [h_q] at h_head
    --   | cons h t =>
    --     rw [h_q] at h_head
    --     simp at h_head
    --     rw [← h_head]
    --     apply List.mem_cons_self
    -- have h_hd_bound : i_2 ≤ hd := (dist_bounds hx hy hd h_head_in).1
    -- grind
    sorry

  case all_valid.entry =>
    -- Goal: AllValidPaths [(sx, sy, 0)] (sx, sy)
    -- Previous proof:
    -- intros x y d h_in
    -- simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h_in
    -- rw [h_in.1, h_in.2.1, h_in.2.2]
    -- exact ValidPath.zero
    sorry

  case queue_shortest.entry =>
    -- Goal: QueueShortest [(sx, sy, 0)] (sx, sy)
    -- Previous proof:
    -- intros x y d h_in d' h_path
    -- simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h_in
    -- rw [h_in.2.2]
    -- exact Nat.zero_le _
    sorry

  case sorted.entry =>
    -- Goal: IsSorted [(sx, sy, 0)]
    -- Previous proof:
    -- rw [IsSorted]
    -- aesop
    sorry

  case visited_complete.entry =>
    -- Goal: VisitedCompleteQueue [(sx, sy)] (sx, sy) [(sx, sy, 0)]
    -- Previous proof:
    -- rw [VisitedCompleteQueue, VisitedComplete]
    -- intros x y k h_path h_le
    -- simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
    -- replace h_le : k = 0 := by grind
    -- rw [h_le] at h_path
    -- cases h_path
    -- aesop
    sorry

  case closed.entry =>
    -- Goal: ClosedSet [(sx, sy)] [(sx, sy, 0)]
    -- Previous proof:
    -- rw [ClosedSet]
    -- aesop
    sorry


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
