import Auto
import Aesop
import Lean
import Mathlib

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"
set_option loom.solver "cvc5"
set_option auto.smt.timeout 3
set_option maxHeartbeats 100000
set_option auto.smt.trust true



method quicksort_list_perm (l : List Int) return (res : List Int)
  ensures List.Sorted (· ≤ ·) res
  ensures List.Perm res l

  do
    if l.length ≤ 1 then
      return l
    else
      -- Pick the first element as pivot
      let pivot := l.head!
      let tail := l.tail!
      let n := tail.length

      -- Partition imperatively using a loop
      let mut lts : List Int := []
      let mut eqs : List Int := [pivot]
      let mut gts : List Int := []
      let mut i : Nat := 0

      -- Loop through tail to partition elements
      while i < n
        invariant hi_bound : i ≤ n
        invariant hi_len : n = tail.length
        -- Track lengths for iteration bound
        invariant h_lts_len : lts.length ≤ i
        invariant h_eqs_len : eqs.length ≤ i + 1
        invariant h_gts_len : gts.length ≤ i
        -- Direct bounds on lts and gts lengths relative to l.length for termination
        invariant h_lts_bound : lts.length < l.length
        invariant h_gts_bound : gts.length < l.length
        -- The three partitions plus unprocessed elements form a permutation of l
        invariant h_perm : List.Perm (lts ++ eqs ++ gts ++ tail.drop i) l
        -- All elements in lts are less than pivot
        invariant h_lts : ∀ x, x ∈ lts → x < pivot
        -- All elements in eqs equal pivot
        invariant h_eqs : ∀ x, x ∈ eqs → x = pivot
        -- All elements in gts are greater than pivot
        invariant h_gts : ∀ x, x ∈ gts → x > pivot
        decreasing dec : n - i
      do
        let elem := tail.get! i
        if elem < pivot then
          lts := lts ++ [elem]
        else
          if elem = pivot then
            eqs := eqs ++ [elem]
          else
            gts := gts ++ [elem]
        i := i + 1

      -- Use decidable conditions to introduce termination facts at term level
      if lts.length < l.length ∧ gts.length < l.length then

        let sorted_lts ← quicksort_list_perm lts
        let sorted_gts ← quicksort_list_perm gts
        -- Concatenate results
        return sorted_lts ++ eqs ++ sorted_gts
      else
          -- This case is impossible given invariants, but needed for termination
          return lts ++ eqs ++ gts
  termination_by l.length
  decreasing_by
    all_goals aesop


-- Helper lemma for sorted lists where all elements are equal



theorem sorted_eq_of_forall_eq {l : List Int} (h : ∀ a ∈ l, a = l.head!) :
    List.Sorted (· ≤ ·) l := by
  induction l with
  | nil => simp [List.Sorted]
  | cons x xs ih =>
    simp only [List.sorted_cons]
    constructor
    · intro a ha
      have hx : x = (x :: xs).head! := rfl
      have ha' : a = (x :: xs).head! := h a (List.mem_cons_of_mem x ha)
      rw [hx, ha']
    · apply ih
      intro a ha
      have : a = (x :: xs).head! := h a (List.mem_cons_of_mem x ha)
      cases xs with
      | nil => simp at ha
      | cons y ys =>
        have hy : y = (x :: y :: ys).head! := h y (by simp)
        simp [List.head!, hy]
        exact this

-- Helper to rewrite drop as cons


theorem drop_eq_get_cons {l : List Int} {i : Nat} (hi : i < l.length) :
    l.drop i = l[i] :: l.drop (i + 1) :=
  List.drop_eq_getElem_cons hi

-- Helper for get! = getElem when in bounds


theorem get_bang_eq_getElem {l : List Int} {i : Nat} (hi : i < l.length) :
    l.get! i = l[i] := by
  aesop

-- Helper for sorted append


theorem sorted_append_of_sorted {l₁ l₂ : List Int}
    (h₁ : List.Sorted (· ≤ ·) l₁) (h₂ : List.Sorted (· ≤ ·) l₂)
    (h : ∀ a ∈ l₁, ∀ b ∈ l₂, a ≤ b) : List.Sorted (· ≤ ·) (l₁ ++ l₂) := by
  induction l₁ with
  | nil => simp [h₂]
  | cons x xs ih =>
    simp only [List.cons_append, List.sorted_cons]
    simp only [List.sorted_cons] at h₁
    constructor
    · intro a ha
      cases List.mem_append.mp ha with
      | inl hxs => exact h₁.1 a hxs
      | inr hl₂ => exact h x (by simp) a hl₂
    · apply ih h₁.2
      intro a ha b hb
      exact h a (List.mem_cons_of_mem x ha) b hb

-- Permutation helper


theorem perm_move_single_to_end {a : Int} {l₁ l₂ : List Int} :
    (l₁ ++ [a] ++ l₂).Perm (l₁ ++ l₂ ++ [a]) := by
  simp only [List.append_assoc]
  apply List.Perm.append_left
  exact List.perm_append_comm


set_option maxHeartbeats 0 in
set_option auto.smt.timeout 3 in
prove_correct quicksort_list_perm
  termination_by l.length
  decreasing_by
    all_goals aesop
  by

  loom_solve

  -- Entry invariants for empty lists
  case h_lts.entry_neg => cases h
  case h_gts.entry_neg => cases h
  case h_eqs.entry_neg => simp only [List.mem_singleton] at h; exact h
  -- Initial lengths
  case h_lts_len.entry_neg => simp
  case h_eqs_len.entry_neg => simp
  case h_gts_len.entry_neg => simp
  case h_lts_bound.entry_neg => simp; omega
  case h_gts_bound.entry_neg => simp; omega
  -- Initial permutation
  case h_perm.entry_neg =>
    have hne : l ≠ [] := by intro heq; simp [heq] at if_neg
    simp only [List.drop_zero, List.nil_append, List.singleton_append, List.append_nil]
    rw [← List.head_cons_tail l hne]
    simp [List.head!, List.tail!]
  -- Base case sorted
  case «ensures» =>
    match l with
    | [] => simp [List.Sorted]
    | [x] => simp [List.Sorted, List.pairwise_singleton]
    | _ :: _ :: _ => simp at if_pos
  -- Base case permutation
  case ensures_1 =>
    exact List.Perm.refl l
  -- Loop invariant maintenance for lengths
  case h_lts_len.loop_pos => simp [List.length_append]; omega
  case h_eqs_len.loop_neg_pos => simp [List.length_append]; omega
  case h_gts_len.loop_neg_neg => simp [List.length_append]; omega
  case h_lts_bound.loop_pos =>
    have h1 : lts.length < l.tail!.length := Nat.lt_of_le_of_lt h_lts_len if_pos_1
    have h2 : lts.length + 1 ≤ l.tail!.length := Nat.succ_le_of_lt h1
    have h3 : l.tail!.length < l.length := by
      cases l with
      | nil => simp at if_neg
      | cons _ _ => simp [List.tail!]
    simp only [List.length_append, List.length_singleton]
    exact Nat.lt_of_le_of_lt h2 h3
  case h_gts_bound.loop_neg_neg =>
    have h1 : gts.length < l.tail!.length := Nat.lt_of_le_of_lt h_gts_len if_pos
    have h2 : gts.length + 1 ≤ l.tail!.length := Nat.succ_le_of_lt h1
    have h3 : l.tail!.length < l.length := by
      cases l with
      | nil => simp at if_neg_1
      | cons _ _ => simp [List.tail!]
    simp only [List.length_append, List.length_singleton]
    exact Nat.lt_of_le_of_lt h2 h3
  -- h_lts.loop_pos
  case h_lts.loop_pos =>
    simp only [List.mem_append, List.mem_singleton] at h
    cases h with
    | inl hl => exact h_lts x hl
    | inr hr =>
      rw [hr]
      have hi : i < l.tail!.length := if_pos_1
      rw [get_bang_eq_getElem hi]
      have := if_pos
      rwa [get_bang_eq_getElem hi] at this
  -- h_eqs.loop_neg_pos
  case h_eqs.loop_neg_pos =>
    simp only [List.mem_append, List.mem_singleton] at h
    cases h with
    | inl hl => exact h_eqs x hl
    | inr hr =>
      rw [hr]
      have hi : i < l.tail!.length := if_pos_1
      rw [get_bang_eq_getElem hi]
      have := if_pos
      rwa [get_bang_eq_getElem hi] at this
  -- h_gts.loop_neg_neg
  case h_gts.loop_neg_neg =>
    simp only [List.mem_append, List.mem_singleton] at h
    cases h with
    | inl hl => exact h_gts x hl
    | inr hr =>
      rw [hr]
      have hi : i < l.tail!.length := if_pos
      rw [get_bang_eq_getElem hi]
      have h1 := if_neg_2
      have h2 := if_neg
      rw [get_bang_eq_getElem hi] at h1 h2
      omega
  -- h_perm.loop_pos
  case h_perm.loop_pos =>
    have hi' : i < l.tail!.length := if_pos_1
    have hdrop := drop_eq_get_cons hi'
    have hget := get_bang_eq_getElem hi'
    rw [hget]
    apply List.Perm.trans _ h_perm
    rw [hdrop]
    simp only [List.append_assoc, List.singleton_append]
    apply List.Perm.append_left
    grind

  -- h_perm.loop_neg_pos
  case h_perm.loop_neg_pos =>
    have hi' : i < l.tail!.length := if_pos_1
    have hdrop := drop_eq_get_cons hi'
    have hget := get_bang_eq_getElem hi'
    rw [hget]
    apply List.Perm.trans _ h_perm
    rw [hdrop]
    simp only [List.append_assoc, List.singleton_append, List.cons_append]
    apply List.Perm.append_left
    apply List.Perm.append_left
    apply List.Perm.symm
    grind
  -- h_perm.loop_neg_neg
  case h_perm.loop_neg_neg =>
    have hi' : i < l.tail!.length := if_pos
    have hdrop := drop_eq_get_cons hi'
    have hget := get_bang_eq_getElem hi'
    rw [hget]
    apply List.Perm.trans _ h_perm
    rw [hdrop]
    simp only [List.append_assoc, List.singleton_append, List.cons_append]
    apply List.Perm.append_left
    apply List.Perm.append_left
    apply List.Perm.append_left
    apply List.Perm.symm
    grind
  -- Final permutation (ensures_1_1)
  case ensures_1_1 =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h_1
    have hdone : i_3 = l.tail!.length := by omega
    have hdrop : List.drop i_3 l.tail! = [] := by simp [hdone]
    apply List.Perm.trans _ h_perm
    simp only [hdrop, List.append_nil]
    exact List.Perm.append (List.Perm.append ensures_1_1 (List.Perm.refl _)) ensures_1
  -- Final sorted (ensures_1)
  case «ensures_1» =>
    -- Extract equalities from h_1: eqs = i_1, gts = i_2, lts_1 = lts
    obtain ⟨h_eqs_eq, h_gts_eq, _, h_lts_eq⟩ := h_1

    -- All elements in x_1 are < pivot (via permutation from lts)
    have h_x1_lt : ∀ a ∈ x_1, a < l.head! := fun a ha =>
      h_lts a (h_lts_eq ▸ ensures_1_1.mem_iff.mp ha)

    -- All elements in i_1 equal pivot
    have h_i1_eq : ∀ a ∈ i_1, a = l.head! := fun a ha =>
      h_eqs a (h_eqs_eq ▸ ha)

    -- All elements in x are > pivot (via permutation from gts)
    have h_x_gt : ∀ a ∈ x, a > l.head! := fun a ha =>
      h_gts a (h_gts_eq ▸ ensures_1.mem_iff.mp ha)

    -- i_1 is sorted (all elements equal the same value)
    have hsorted_i1 : List.Sorted (· ≤ ·) i_1 := by
      cases hi1 : i_1 with
      | nil => exact List.sorted_nil
      | cons e es =>
        apply sorted_eq_of_forall_eq
        intro a ha
        have he : e = l.head! := by aesop
        have ha' : a = l.head! := h_i1_eq a (hi1 ▸ ha)
        simp only [List.head!_cons]
        rw [ha', he]

    -- x_1 ++ i_1 is sorted
    have hsorted_x1_i1 : List.Sorted (· ≤ ·) (x_1 ++ i_1) := by
      apply sorted_append_of_sorted ensures_2 hsorted_i1
      intro a ha b hb
      have ha' : a < l.head! := h_x1_lt a ha
      have hb' : b = l.head! := h_i1_eq b hb
      rw [hb']
      exact le_of_lt ha'

    -- (x_1 ++ i_1) ++ x is sorted
    apply sorted_append_of_sorted hsorted_x1_i1 «ensures»
    intro a ha b hb
    have hb' : b > l.head! := h_x_gt b hb
    cases List.mem_append.mp ha with
    | inl hx1 =>
      have ha' : a < l.head! := h_x1_lt a hx1
      exact le_of_lt (lt_trans ha' hb')
    | inr hi1 =>
      have ha' : a = l.head! := h_i1_eq a hi1
      rw [ha']
      exact le_of_lt hb'
  case «ensures_2» =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact absurd ⟨h_lts_bound, h_gts_bound⟩ if_neg


#eval (quicksort_list_perm [2, 1, 3, 4, 5, 7, 6, 9, 11, 10, 14, 13]).extract
