import Auto

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

/-!
# Naming Tests for Velvet

This file demonstrates and tests the naming functionality in Velvet programs.

## Named Clauses

Velvet supports optional naming for the following clauses:

| Clause       | Unnamed Syntax           | Named Syntax                  |
|--------------|--------------------------|-------------------------------|
| `require`    | `require cond`           | `require name: cond`          |
| `ensures`    | `ensures cond`           | `ensures name: cond`          |
| `invariant`  | `invariant cond`         | `invariant name: cond`        |
| `assert`     | `assert cond`            | `assert name: cond`           |
| `decreasing` | `decreasing measure`     | `decreasing name: measure`    |
| `done_with`  | `done_with cond`         | `done_with name: cond`        |

## Goal Tag Suffixes

For loop invariants, goals are tagged with semantic suffixes:
- `.entry` - The invariant must hold when entering the loop
- `.loop` - The invariant must be preserved by each iteration
- `.exit` - The invariant holds at loop exit

For example, `invariant h2: i <= n` generates goals `h2.entry` and `h2.loop`.

## Benefits

1. **Proof Stability**: Named goals don't change when unrelated code changes
2. **Readability**: `case h2.loop` is more meaningful than `case ?_`
3. **Cacheability**: Lean's incremental compilation can cache individual case proofs
4. **Maintainability**: When invariants change, only affected cases need updates

The file is organized into sections:
1. Demonstration - A worked example with case-based proofs
2. Partial Correctness Tests
3. Total Correctness Tests
4. Edge Cases and Collision Tests
-/

section Demonstration

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

/- A simple method that computes `number1 + number2` using a loop.
   All verification conditions are explicitly named for stable proofs. -/
method NamingDemo (number1 : Nat) (number2: Nat) return (sum: Nat)
    require r1 : number1 < number2
    ensures e1 : sum = number1 + number2
do
    let mut sum := number1
    let mut i := 0
    while i < number2
      invariant h1: sum = number1 + i
      invariant h2: i <= number2
      decreasing dec1: number2 - i
    do
        sum := sum + 1
        i := i + 1
    assert assert1: sum = number1 + number2
    return sum

/- The proof uses `case` to target specific named goals.
   This makes the proof resilient to changes in other parts of the program. -/
prove_correct NamingDemo by
    loom_goals_intro
    loom_named_split
    all_goals loom_unfold
    case h1.loop =>
        loom_solver
    case assert1 =>
        loom_solver
    all_goals loom_solver

end Demonstration

/- Use custom solver so goals remain unsolved for inspection -/

macro_rules
  | `(tactic| loom_solver) => `(tactic| skip)

section PartialCorrectness

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Test: Unnamed require and ensures -/
method test_unnamed_require_ensures (x: ℕ) return (res: ℕ)
    require x > 0
    ensures res = x - 1 + 1
    do
    return x

prove_correct test_unnamed_require_ensures by
    loom_solve
    sorry

/- Test: Named require and ensures -/
method test_named_require_ensures (x: ℕ) return (res: ℕ)
    require pre1: x > 0
    ensures post1: res = x - 1 + 1
    do
    return x

prove_correct test_named_require_ensures by
    loom_solve
    all_goals sorry

/- Test: Multiple named and unnamed require/ensures -/
method test_multiple_clauses (x: ℕ) (y: ℕ) return (res: ℕ)
    require in1: x > 0
    require in2: y > 0
    require x + y > 1
    ensures out1: res = x + y
    ensures res > 0
    ensures res ≤ x + y
    do
    return x + y

prove_correct test_multiple_clauses by
    loom_solve
    all_goals sorry

/- Test: Unnamed invariant and done_with -/
method test_unnamed_invariant (x: ℕ) return (res: ℕ)
    require x > 0
    ensures res ≤ x
    do
    let mut i := x
    while i > 0
    invariant i ≤ x
    done_with i = 0
    do
        i := i - 1
    return i

prove_correct test_unnamed_invariant by
    loom_solve
    all_goals sorry

/- Test: Named invariants and done_with -/
method test_named_invariant (x: ℕ) return (res: ℕ)
    require x > 0
    ensures res ≤ x
    do
    let mut i := x
    while i > 0
    invariant loop_invariant: i ≤ x
    done_with loop_done_with: i = 0
    do
        i := i - 1
    return i

prove_correct test_named_invariant by
    loom_solve
    all_goals sorry

/- Test: Multiple invariants -/
method test_multiple_invariants (x: ℕ) return (res: ℕ)
    require x > 0
    ensures res ≤ x
    do
    let mut i := x
    let mut sum := 0
    while i > 0
    invariant bound: i ≤ x
    invariant sum_inv: sum ≤ x - i
    invariant i + sum ≤ x
    invariant x = x - 1 + 1
    done_with exit_cond: i = 0
    do
        sum := sum + 1
        i := i - 1
    return sum

prove_correct test_multiple_invariants by
    loom_solve
    all_goals sorry

/- Test: Mix of named and unnamed in same method -/
method test_mixed_naming (x: ℕ) (y: ℕ) return (res: ℕ)
    require precond1: x > 0
    require y > 0
    ensures postcond1: res > 0
    ensures res = x + y
    do
    let mut i := x
    while i < x + y
    invariant named_inv: i ≥ x
    invariant i ≤ x + y
    done_with named_done: i = x + y
    do
        assert mid_check: i < x + y
        i := i + 1
    return i

prove_correct test_mixed_naming by
    loom_solve
    all_goals sorry

end PartialCorrectness

section TotalCorrectness

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

/- Test: Unnamed decreasing clause -/
method test_unnamed_decreasing (x: ℕ) return (res: ℕ)
    require x > 0
    ensures res = 0
    do
    let mut i := x
    while i > 0
    invariant i ≤ x
    done_with i = 0
    decreasing i
    do
        i := i - 1
    return i

prove_correct test_unnamed_decreasing by
    loom_solve
    all_goals sorry

/- Test: Named decreasing clause -/
method test_named_decreasing (x: ℕ) return (res: ℕ)
    require x > 0
    ensures res = 0
    do
    let mut i := x
    while i > 0
    invariant bound: i ≤ x
    done_with exit: i = 0
    decreasing measure: i
    do
        i := i - 1
    return i

prove_correct test_named_decreasing by
    loom_solve
    case measure =>
        sorry
    all_goals sorry

/- Test: Full naming in total correctness -/
method test_full_naming_total (n: ℕ) return (res: ℕ)
    require input_valid: n > 0
    ensures output_zero: res = 0
    ensures output_bound: res ≤ n
    do
    let mut i := n
    while i > 0
    invariant loop_bound: i ≤ n
    invariant loop_nonneg: i ≥ 0
    done_with loop_exit: i = 0
    decreasing loop_measure: i
    do
        assert i > 0
        let k :| k < i
        i := i - 1
    return i

prove_correct test_full_naming_total by
    loom_solve
    all_goals sorry

end TotalCorrectness

section EdgeCases

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Test: Same name used for different clause types -/
method test_same_name_different_types (x: ℕ) return (res: ℕ)
    require check: x > 0
    ensures check: res = x
    do
    let mut i := x
    while i > 0
    invariant check: i ≤ x
    done_with check: i = 0
    do
        assert check: i > 0
        i := i - 1
    return 0

prove_correct test_same_name_different_types by
    loom_solve
    all_goals sorry

end EdgeCases

section NestedLoops

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Test: Nested loops - verifies that inner loop phases are correctly tracked

   For nested loops, the naming system needs to properly track loop depth:
   - Outer loop invariants get `.entry`, `.loop`, `.exit` suffixes
   - Inner loop invariants also get `.entry`, `.loop`, `.exit` suffixes
-/
method test_nested_loops (n: ℕ) (m: ℕ) return (res: ℕ)
    require n_pos: n > 0
    require m_pos: m > 0
    ensures result: res = n * m
    do
    let mut total := 0
    let mut i := 0
    -- Outer loop
    while i < n
    invariant outer_bound: i ≤ n
    invariant outer_sum: total = i * m
    done_with outer_done: i = n
    do
        let mut j := 0
        -- Inner loop
        while j < m
        invariant inner_bound: j ≤ m
        invariant inner_sum: total = i * m + j
        done_with inner_done: j = m
        do
            if total = 0 then
                total := 1
            else
                total := total + 1
            j := j + 1
        i := i + 1
    return total

prove_correct test_nested_loops by
    loom_solve
    all_goals sorry

/- Test: Deeply nested loops (3 levels) -/
method test_deeply_nested_loops (a: ℕ) (b: ℕ) (c: ℕ) return (res: ℕ)
    require a_pos: a > 0
    require b_pos: b > 0
    require c_pos: c > 0
    ensures result: res = a * b * c
    do
    let mut total := 0
    let mut i := 0
    while i < a
    invariant level1: i ≤ a
    do
        let mut j := 0
        while j < b
        invariant level2: j ≤ b
        do
            let mut k := 0
            while k < c
            invariant level3: k ≤ c
            do
                total := total + 1
                let (z : ℕ) :| z < j
                k := k + 1
            j := j + 1
        i := i + 1
    return total

prove_correct test_deeply_nested_loops by
    loom_solve
    all_goals sorry

end NestedLoops
