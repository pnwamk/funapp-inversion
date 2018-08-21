# simple semantic subtyping model

Some haskell code to implement some simple semantic subtyping algorithms.

For more info on how to implement such systems, see the following (those works include
references to the more theoretical foundations of this work):

- Giuseppe Castagna. Covariance and Contravariance: a fresh look at an old issue (a primer in advanced type systems for learning functional programmers). 2013. Unpublished manuscript, periodically updated. (a link should be found here https://www.irif.fr/~gc/)

- Andrew M. Kent. Down and Dirty with Semantic Set-theoretic Types (a tutorial). 2018. Unpublished, periodically updated. https://pnwamk.github.io/sst-tutorial/




## File/Directory descriptions

### `src/Commom/`

Not much in here at the moment.

#### `src/Common/SetOps.hs`

Some misc set-theory operations.

### `src/Commom/Types/`

Contains type definitions (syntax and internal rep),
many metafunctions that operate over types, and
types for various numeric Racket operations.

#### `src/Types/Syntax.hs`

Defines the datatype for the user-level syntax of types
(`Ty`) which roughly equates to the following:

```haskell
data Ty =
        T -- true
      | F -- false
      | NumericBaseType0
      | ...
      | NumericBaseTypeN
      | Prod Ty Ty
      | Arrow Ty Ty
      | Or [Ty]
      | And [Ty]
      | Not Ty
      | Any
      | Empty
```

Also defines a few other datatypes for representing Typed
Racket functions.


Then goes on to define all of the various unions which make
up Typed Racket's numeric tower, e.g.:

```haskell
number = Or [real, imaginary, exactComplex, inexactComplex]
```

and then defines some data structures we use to iterate over
all the numeric types (e.g. `numericTypes`) for testing and such.

Finally, defines `Arbitrary` for `Ty` since we use
QuickCheck to do lots of testing.


#### `src/Types/Base.hs`

Defines the low-level representation for the base portion of
types.

#### `src/Types/LazyBDD.hs`

Defines the low-level representation for types (lazy binary
decision diagrams) and basic operations on them (union,
intersection, negation, etc).

#### `src/Types/Subtype.hs`

Defines _efficient_ type emptiness calculation (which is how
subtyping, equivalence, and more are defined).

#### `src/Types/NSubtype.hs`

Defines _inefficient_ type emptiness calculation (which is
how subtyping, equivalence, and more are defined). The
definitions in this module are much closer to the raw math
definitions given in Castagna's and Kent's unpublished
tutorials.

#### `src/Types/Metafunctions.hs`

Contains _efficient_ implementations of type metafuntions,
e.g.  product projection calculation, function application
calculation, etc.

#### `src/Types/NMetafunctions.hs`

Contains _inefficient_ implementations of type metafuntions,
e.g.  product projection calculation, function application
calculation, etc. The definitions in this module are much
closer to the raw math definitions given in Castagna's and
Kent's unpublished tutorials.

#### `src/Types/SyntacticOpTypes.hs`

Types for Racket primitives meant for use with syntactic
Typed Racket v7.0 style reasoning. E.g., `+` is defined to
have _many_ arrows, and when type checking an application,
Typed Racket tries them _in order_ and uses the codomain
from the _first_ arrow which can be applied for the
resulting type.

#### `src/Types/SyntacticOpTypesPlus.hs`

Types for Racket primitives meant for use with _slightly
improved_ syntactic Typed Racket v7.0 style reasoning. E.g.,
`+` is defined to have _many fewer_ arrows than in
`SyntacticOpTypes.hs`, with the intent that when type
checking an application, Typed Racket tries all arrows and
intersects the codomain from _each applicable arrow_ to
determine the resulting type.

#### `src/Types/SemanticOpTypes.hs`

Types for Racket primitives meant for use with full semantic
type reasoning (a la CDuce).

#### `src/Types/CompareOpTypes.hs`

Functions for comparing the types defined in `*OpTypes.hs`
files and reporting if they are in sync, etc.

### `test/Commom/Types/`

Contains all the automated testing for the type and
metafunction implementations (i.e. compares the inefficient
and efficient implementations of the various operations to
make sure they match up).

#### `test/Types/MetafunctionTests.hs`

Parameterizable test suite for type metafunctions to test
for correctness.

#### `test/Types/MetafunctionsCompSpec.hs`

Test suite to compare efficient and inefficient metafunction
implementations.

#### `test/Types/MetafunctionsSpec.hs`

`test/Types/MetafunctionTests.hs` tests instantiated with
the efficient implementation.

#### `test/Types/NMetafunctionsSpec.hs`

`test/Types/MetafunctionTests.hs` tests instantiated with
the inefficient implementation.

#### `test/Types/SubtypeTests.hs`

Parameterizable test suite for type inhabitation/subtyping
to test for correctness.

#### `test/Types/SubtypeCompSpec.hs`

Test suite to compare efficient and inefficient
inhabitation/subtyping implementations.

#### `test/Types/SubtypeSpec.hs`

`test/Types/SubtypeTests.hs` tests instantiated with
the efficient implementation.

#### `test/Types/NSubtypeSpec.hs`

`test/Types/SubtypeTests.hs` tests instantiated with
the inefficient implementation.
