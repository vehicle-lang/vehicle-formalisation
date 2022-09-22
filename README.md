# Vehicle Formalisation

This is an Agda formalisation of a core subset of the Vehicle language
and a normalisation procedure from the higher order language down to
constraint terms suitable for an SMT solver.

Agda modules (in `src`):

- `MiniVehicle` : The syntax of "Mini Vehicle" using intrinsically
  typed abstract syntax. This includes higher order functions, linear
  expressions, boolean constraints and if-then-else. Currently missing
  are uninterpreted functions and quantifiers.
- `Interpretation` : defines the general notion of 'model' for
  MiniVehicle, which is used by the `StandardSemantics`,
  `Normalisation` and `NormalisationCorrect` modules.
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
  proof is accomplished using a Kripke logical relation. The final
  definition `full-correctness` is the proof of Theorem 4.1 in the
  paper.

- `Everything` : import the main modules to make sure everthing gets
  checked, and to provide an index.

Auxillary modules:

- `EquiInhabited` : some combinators for writing proofs of
  equihabited-ness of sets, used in `NormalisationCorrect`.
- `Util` : two lemmas that could be in the standard library.

## Requirements

The easiest way to install the requirements and build the HTML version
is to use [Nix](https://nixos.org/). If the `nix` command line tool is
installed, and the flake feature is enabled (see 'TRYING OUT FLAKES'
in [https://www.tweag.io/blog/2020-05-25-flakes/]), then typing:

    nix build

will check the development and place the resulting HTML rendering in a
folder called `result`.

If you have `nix`, but don't want to enable Flakes. Then you can type

    nix-shell

To temporarily install the dependencies. Then run the `agda` command
below.

Without using `nix` the following two packages need to be installed on
your system:

- Agda 2.6.2.2 [https://wiki.portal.chalmers.se/agda/Main/Download]
- Agda standard library 1.7.1 [https://wiki.portal.chalmers.se/agda/Libraries/StandardLibrary]

If both of these are installed properly, then it should be possible to
run

    agda --html --html-dir=html src/Everything.agda

to check the development and generate an HTML formatted version in a
`html/` directory.


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
