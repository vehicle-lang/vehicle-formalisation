# Vehicle Formalisation

This is an Agda formalisation of a core subset of the Vehicle language
and a normalisation procedure from the higher order language down to
constraint terms suitable for an SMT solver.

Agda modules:

- `MiniVehicle` : The syntax of "Mini Vehicle" using intrinsically
  typed abstract syntax. This includes higher order functions, linear
  expressions, boolean constraints and if-then-else. Currently missing
  are uninterpreted functions and quantifiers.
- `StandardSemantics` : The standard semantics of Vehicle, where
  numbers are interpreted as rationals and constraints as boolean
  valued predicates.
- `NormalisedExpr` : The expressions in "normal form" suitable for
  sending to an SMT solver. This includes the special `let` and `if`
  lifting monad used for normalisation.
- `Normalisation` : A Normalisation-by-Evaluation procedure for
  normalising MiniVehicle to SMT expressions.
- `NormalisationCorrect` : A proof that the semantics of the
  normalised expressions agrees with the standard semantics. This
  proof is accomplished using a Kripke logical relation.

## TODO

- [X] Port the proof that the two semantics agree on closed terms of
      type `Bool constraint`
- [ ] Add quantifiers to MiniVehicle
  - [X] Existential quantifiers over rationals
  - [ ] Quantifiers over container types, reduced to nested quantification
  - [ ] Quantification over Indexes (via `reduce`)
- [X] Uninterpreted functions to MiniVehicle
- [X] Type-level quantification over array sizes
  - [X] Syntax
  - [X] Standard Semantics
  - [X] Normalising Semantics
  - [X] Correctness Relation
- [ ] Add tuple types to MiniVehicle
- [ ] Add array types to MiniVehicle
  - [X] Add basic array types and indexes
  - [X] Add size and index constants
  - [ ] Add `reduce` (a.k.a. `Foldable.fold`)
