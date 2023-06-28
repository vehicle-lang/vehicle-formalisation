module Everything where

{------------------------------------------------------------------------------

          MiniVehicle

  ------------------------------------------------------------------------------}


{- MiniVehicle is a typed language designed for writing specifications of neural
   network components of AI-powered systems. The language has multiple
   interpretation backends to:

     -

   The core language is a typed λ-calculus with indexed types. To fulfil its
   purpose as a specification language, MiniVehicle also includes:

     - Uninterpreted functions, used to represent "systems under analysis", such
       as neural networks. "Uninterpreted" refers to the fact that they are not
       given an interpretation by MiniVehicle itself.

     - Arithmetic and numeric comparisons operators.

     - Vectors, with lengths statically represented using indexed types. Indexing
       is statically checked to always be within bounds.

     - Polymorphic if-then-else conditional.

     - Logical operators, including existential quantification.

   The syntax of MiniVehicle is defined in stages: kinds, types, then terms. We
   use an intrinsically typed representation of the syntax. The data types
   defining the typed syntax of each layer are all imported via the
   MiniVehicle.Language.Syntax module: -}
import MiniVehicle.Language.Syntax
{- Since not all backends support all of the operators above, MiniVehicle is
   actually a family of languages where the features that are available are
   controlled by means of indexed types and explicit evidence passing of the
   capability to use each feature. Each instantiation of the language is defined
   in terms of a "Restriction" record, defined in the following module: -}
import MiniVehicle.Language.Syntax.Restriction

{- MiniVehicle is a language constructed to have multiple interpretations. To
   save us the work of building each interpretation from scratch, we define a
   generic notion of model of MiniVehicle, indexed by the kinds of Restrictions
   in play.

   The definition of model is built around ideas from Categorical Logic. Roughly
   speaking, the interpretation is into some (indexed) category where types are
   interpreted as objects and terms are interpreted as morphisms. Interpretations
   of all the additional operators of MiniVehicle are required, depending on the
   Restrictions currently applied.

   Anticipating the needs of the interpretation that normalises specifications
   to a form suitable for neural network verifiers, we also require each Model to
   define a strong monad to allow for the possibility of additional effects
   during intepretation. -}
import MiniVehicle.Language.Model

{- Given a Model, we can interpret MiniVehicle terms. Other than the direct
   translation of terms into morphisms in the model, we use Moggi's Call-by-Value
   monadic translation to allow for non-local interpretations of some constructs.
   This feature is crucially applied by the normalisation procedure defined
   below. -}
import MiniVehicle.Language.Interpretation

{- Our first model of MiniVehicle is the "standard semantics" that interprets all
   the constructs of the language in the "standard" way. That is, functions are
   interpreted as functions, numbers are interpreted as rational numbers and
   properties are interpreted as booleans.

   We will use this semantics as the reference semantics for the following
   semantics to specify their correctness properties. For each of the alternative
   backends we have a further interpretation of that backend, such that their
   composition must be correctly related to this reference semantics. We elaborate
   further below. -}
import MiniVehicle.Language.StandardSemantics

{- Normalisation backend: TODO -}
import MiniVehicle.Verifiers.Normalisation
import MiniVehicle.Verifiers.NormalisationCorrect

{- Loss Function / Quantitative Logic backend: TODO -}
import MiniVehicle.LossFunctions.GenericCompilation
import MiniVehicle.LossFunctions.GenericCorrectness
import MiniVehicle.LossFunctions.Instantiation1
-- import MiniVehicle.LossFunctions.Instantiation2
