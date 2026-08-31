module Logic.FunctionalProbability

import Data.List
import Math.Multiset
import Math.Singleton.Sing
import Math.Interfaces
import Math.Singleton.Bit
import Logic.Bridge
import Core.BoxInt
import Core.UnixelFraction
import Core.VexelMaxel

%default total

-----------------------------------------------------------------------
-- HEHNER FUNCTIONAL PROBABILITY OVER VEXEL SPACES
--
-- Eric Hehner replaces infinite quantifiers (∀, ∃) with calculational
-- min/max over closed finite spaces. Probability is not an axiom
-- but a derived normalisation:
--   P(x) = weight(x) / totalMass
-----------------------------------------------------------------------

||| Probability fraction alias.
public export
0 MSetFraction : Type
MSetFraction = SingFraction

||| Computes total weight sum over a Vexel state vector.
public export
vexelTotalMass : Vexel -> BoxInt
vexelTotalMass (MkVexel terms) = foldl (\acc, (_, w) => acc + w) 0 terms

||| Extract state probability from weight and total mass.
public export
stateProbability : BoxInt -> BoxInt -> SingFraction
stateProbability num den =
  mkUnixelFraction num (Math.Interfaces.integerToNat den.value)

||| Exact expectation of a payload function over a discrete Vexel.
public export
expectation : (Unixel -> BoxInt) -> Vexel -> SingFraction
expectation f (MkVexel terms) =
  let weightedSum = foldl (\acc, (u, w) => acc + (f u * w)) 0 terms
      totMass = foldl (\acc, (_, w) => acc + w) 0 terms
  in stateProbability weightedSum totMass
