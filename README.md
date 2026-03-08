# miniproof

A small dependently-typed proof checker written in Haskell.

## Features

- **Dependent function types** (Pi types): `forall (x : A) -> B`
- **Bidirectional type checking** with NbE (normalization by evaluation)
- **Universe hierarchy**: `Type`, `Type 1`, `Type 2`, … with cumulativity
- **Universe level polymorphism**: quantify over universe levels with `Level`
- **Inductive data types** with dependent constructors
- **Recursive functions** via `fix`
- **Dependent pattern matching** with a return motive
- **Index refinement**: impossible branches are omitted automatically
- **Propositional equality**: `Id`, `refl`, `J`

## Installation

```
cabal build
```

## Usage

```
cabal run miniproof -- file.pf          # type-check a file
cabal run miniproof -- --repl           # start the REPL
cabal run miniproof                     # REPL (default when no files given)
```

## Language

### Types and universes

```
Type          -- Type 0, the universe of small types
Type 1        -- the universe of larger types; Type 0 : Type 1
Type l        -- universe at level l  (l is a Level expression)
Level         -- the type of universe levels
lzero         -- level 0
lsucc l       -- level l + 1
lmax l m      -- maximum of two levels
```

Universe cumulativity holds: if `A : Type k` and `k ≤ j`, then `A : Type j`.

### Functions

```
forall (x : A) -> B    -- dependent function type (Pi type)
A -> B                 -- non-dependent function type (sugar for forall (_ : A) -> B)
\(x : A) -> e          -- lambda abstraction
f e                    -- application
```

### Let bindings

```
let x : A = e in body
```

### Inductive types

```
data Name : Kind where
  { Con1 : T1 -> T2 -> Name
  | Con2 : forall (n : Nat) -> Name
  }
```

### Pattern matching

```
match t return (\(x : T) -> P) with
{ Con1 a b -> e1
| Con2 n   -> e2
}
```

The return motive is a function from the scrutinee type to the result type. Impossible branches (index refinement) can be omitted.

### Recursive functions

```
fix (f : A -> B) (x : A) = body
```

`f` is the self-reference, `x` is the argument. The function has type `A -> B`.

### Propositional equality

```
Id A a b          -- the type of proofs that a = b in A
refl A a          -- proof that a = a
J A a P pr b p    -- J eliminator (path induction)
```

`J` has type:
```
J : forall (A : Type)
  -> forall (a : A)
  -> forall (P : forall (b : A) -> Id A a b -> Type)
  -> P a (refl A a)
  -> forall (b : A)
  -> forall (p : Id A a b)
  -> P b p
```

## Example: level-polymorphic identity

Without level polymorphism, you would need separate `id0`, `id1`, … for each universe. With `Level`, a single definition works at all levels:

```
id : forall (l : Level) -> forall (A : Type l) -> A -> A
   = \(l : Level) -> \(A : Type l) -> \(a : A) -> a
```

Instantiate it at `lzero` for `Bool`:

```
data Bool : Type where { true : Bool | false : Bool }

idBool : Bool -> Bool = id lzero Bool
```

Or at `lsucc lzero` for a function type:

```
idFun : (Bool -> Bool) -> (Bool -> Bool)
      = id (lsucc lzero) (Bool -> Bool)
```

## Example: dependent vectors

`test/fixtures/vec.pf` defines length-indexed vectors:

```
data Vec : Nat -> Type where
  { nil  : Vec zero
  | cons : forall (n : Nat) -> Type -> Vec n -> Vec (succ n)
  }
```

Index refinement makes the `nil` branch of a `cons` pattern automatically impossible.

## Architecture

The implementation uses standard techniques from dependent type theory:

| File | Role |
|------|------|
| `src/Prover/Syntax.hs` | Raw (named), Core (de Bruijn), and Value ASTs |
| `src/Prover/Parser.hs` | Megaparsec parser |
| `src/Prover/Eval.hs` | NbE evaluator, conversion checking, subtyping |
| `src/Prover/Check.hs` | Bidirectional type checker / elaborator |
| `src/Prover/Env.hs` | Typing context |
| `src/Prover/Pretty.hs` | Pretty printer |
| `app/Main.hs` | CLI entry point |
| `app/Repl.hs` | Interactive REPL |

**De Bruijn representation.** Core terms use de Bruijn indices; the evaluator uses de Bruijn levels (absolute) to avoid shifting.

**NbE.** Terms are evaluated to semantic values (`Val`), which are then quoted back to terms for conversion checking or error display. This avoids explicit substitution.

**Level polymorphism.** Universe levels (`LevelExpr`) are a separate syntactic category from terms. Level variables share the ordinary term context and de Bruijn counter. `evalLevel` maps a `LevelExpr` to a `VLevel` using the current environment. `leLevel` implements a sound subtype ordering on `VLevel` that handles `lmax`, `lsucc`, and reflexivity.

**Universe cumulativity.** `subtypeOf` handles `VType l1 ≤ VType l2` when `leLevel l1 l2`, and is covariant/contravariant across Pi types.

**Index refinement.** When pattern-matching, impossible constructor branches are detected by checking whether the constructor's return-type indices are structurally incompatible with the scrutinee's type indices (rigid constructor mismatch).

## Known limitations

- No termination checking (`fix` is trusted).
- No implicit arguments or elaboration of missing level arguments.
- `leLevel` is sound but incomplete for arbitrary level expressions with neutral variables (handles common cases).
- No level metavariables: level arguments must be supplied explicitly.
- Inductive proofs combining `fix` and `J` (e.g. commutativity of addition) hang during type-checking — the checker does not reduce under `fix` during conversion, so recursive equality proofs loop.

## Tests

```
cabal test
```

Test fixtures in `test/fixtures/`:

| File | What it tests |
|------|---------------|
| `basics.pf` | id, const, compose, flip, modus ponens |
| `inductive.pf` | Bool, Nat, pattern matching |
| `recursion.pf` | add, mul, double via fix |
| `vec.pf` | Length-indexed vectors |
| `equality.pf` | sym, trans, cong, subst via J |
| `fin.pf` | Finite sets, index refinement, impossible branches |
| `universe.pf` | Universe cumulativity |
| `levels.pf` | Universe level polymorphism |
