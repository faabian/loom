import Auto

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

/-!
# Named Invariants and Assertions

This file demonstrates how to use **named invariants, assertions, and pre- and postconditions**
to improve proof maintainability and cacheability in Velvet programs.

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
- `.exit` - (if applicable) The invariant holds at loop exit

For example, `invariant h2: i <= number2` generates goals `h2.entry` and `h2.loop`.

## Benefits

1. **Proof Stability**: Named goals don't change when unrelated code changes
2. **Readability**: `case h2.loop` is more meaningful than `case ?_`
3. **Cacheability**: Lean's incremental compilation can cache individual case proofs
4. **Maintainability**: When invariants change, only affected cases need updates

-/

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

-- A simple method that computes `number1 + number2` using a loop.
-- All verification conditions are explicitly named for stable proofs.
method NamingTest (number1 : Nat) (number2: Nat) return (sum: Nat)
    require r1 : number1 < number2      -- Named precondition (not a proof goal)
    ensures e1 : sum = number1 + number2 -- Named postcondition, becomes goal `e1`
do
    let mut sum := number1
    let mut i := 0
    while i < number2
      invariant h1: sum = number1 + i   -- Becomes goals `h1.entry`, `h1.loop`
      invariant h2: i <= number2        -- Becomes goals `h2.entry`, `h2.loop`
      decreasing dec1: number2 - i      -- Named termination measure
    do
        sum := sum + 1
        i := i + 1
    assert assert1: sum = number1 + number2  -- Named assertion, becomes goal `assert1`
    return sum

-- The proof uses `case` to target specific named goals.
-- This makes the proof resilient to changes in other parts of the program.
prove_correct NamingTest by
    loom_goals_intro
    loom_unfold
    case assert1 =>   -- The assertion after the loop
      grind
    case h2.loop =>   -- Loop preservation for invariant h2
      loom_solver
    case h2.entry =>  -- Loop entry condition for invariant h2
      loom_solver
    case e1 =>        -- The postcondition
      grind
    all_goals loom_solver  -- Remaining goals (h1.entry, h1.loop, etc.)
