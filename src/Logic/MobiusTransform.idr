module Logic.MobiusTransform

import Data.List
import Data.Nat
import Math.Multiset
import Math.BoxInt
import Math.SignedFraction
import Math.Interfaces
import Math.OnSeq.OnMSet
import Math.Singleton.Sing
import Math.Singleton.Bit
import Math.Vexel.Byte
import Logic.BoolePolynumber

%default covering

-----------------------------------------------------------------------
-- THE BOOLE-MÖBIUS TRANSFORM
--
-- Source: Wildberger Lectures 270, 271, 272.
--
-- T(i,j) = 1 iff i ⊆ j (subset inclusion via binary encoding).
-- Self-inverse over B₂: T² = I.
-----------------------------------------------------------------------

||| Apply the Boole-Möbius transform.
||| Self-inverse: mobiusTransform (mobiusTransform v) = v.
public export
mobiusTransform : List Bit -> List Bit
mobiusTransform xs =
  let size = length xs
  in map (\i => foldRow i 0 xs) [0 .. minus size 1]
  where
    foldRow : Nat -> Nat -> List Bit -> Bit
    foldRow _ _ [] = Zero
    foldRow i j (x :: rest) =
      let contrib = if isSubsetNat i j then x else Zero
      in addBit contrib (foldRow i (S j) rest)

||| Convert a Boolean function (dense truth table) to Boole polynumber.
public export
boolFuncToBoole : List Bit -> BoolePolynumber
boolFuncToBoole truthTable = denseToSparse (mobiusTransform truthTable)

||| Convert a Boole polynumber to Boolean function (dense truth table).
public export
booleToBoolFunc : (numVars : Nat) -> BoolePolynumber -> List Bit
booleToBoolFunc n poly =
  let dense = sparseToDense (power 2 n) poly
  in mobiusTransform dense

||| Convert an index to a list of Bit inputs of length n.
public export
indexToAssignment : (n : Nat) -> Nat -> List Bit
indexToAssignment Z _ = []
indexToAssignment (S k) j =
  let bit = if isOdd j then One else Zero
  in bit :: indexToAssignment k (half j)

||| Verify that a Boole polynumber is equivalent to its source Boolean function (truth table).
||| For all inputs j ∈ [0, 2^n-1], evalBoolePoly poly (indexToAssignment n j) == truthTable[j].
public export
verifyEquivalence : (n : Nat) -> List Bit -> Bool
verifyEquivalence n truthTable =
  let poly = boolFuncToBoole truthTable
      size = power 2 n
  in all (\j => evalBoolePoly poly (indexToAssignment n j) == lookupBit j truthTable) [0 .. minus size 1]
  where
    lookupBit : Nat -> List Bit -> Bit
    lookupBit _ [] = Zero
    lookupBit Z (x :: _) = x
    lookupBit (S k) (_ :: rest) = lookupBit k rest


-----------------------------------------------------------------------
-- HAILPERIN PROBABILITY BOUNDS (Row 4)
--
-- Source: Theodore Hailperin, "Boole's Logic and Probability" (1986).
--
-- When given incomplete data (fragmentary probabilities), a single
-- exact probability cannot be determined.  Instead, Hailperin showed
-- that Boole's method produces tight interval bounds [min, max]
-- via the inclusion-exclusion principle.
--
-- No LP solver needed — the Boole-Möbius polynomial structure yields
-- the bounds directly by enforcing non-negativity of truth-table weights.
-----------------------------------------------------------------------

||| A closed interval [lo, hi] of MSetFractions.
||| Represents the tightest possible bounds on an unknown probability.
public export
record ProbBounds where
  constructor MkBounds
  lo : MSetFraction
  hi : MSetFraction

public export
Show ProbBounds where
  show (MkBounds l h) = "[" ++ show l ++ ", " ++ show h ++ "]"

public export
Eq ProbBounds where
  (MkBounds l1 h1) == (MkBounds l2 h2) = l1 == l2 && h1 == h2

-----------------------------------------------------------------------
-- TRIVIAL BOUNDS
-----------------------------------------------------------------------

||| The trivial bounds [0/1, 1/1] — no information.
public export
trivialBounds : ProbBounds
trivialBounds = MkBounds zeroMSF oneMSF

||| An exact probability (degenerate interval where lo == hi).
public export
exactBounds : MSetFraction -> ProbBounds
exactBounds p = MkBounds p p

-----------------------------------------------------------------------
-- INTERSECTION OF BOUNDS
-----------------------------------------------------------------------

||| Tighten two intervals by taking the intersection.
||| max(lo₁, lo₂) and min(hi₁, hi₂).
||| Returns Nothing if the intersection is empty (contradiction).
public export
intersectBounds : ProbBounds -> ProbBounds -> Maybe ProbBounds
intersectBounds (MkBounds l1 h1) (MkBounds l2 h2) =
  let newLo = if gtProbability l1 l2 then l1 else l2
      newHi = if gtProbability h1 h2 then h2 else h1
  in if gtProbability newLo newHi
     then Nothing
     else Just (MkBounds newLo newHi)
  where
    gtProbability : MSetFraction -> MSetFraction -> Bool
    gtProbability (MkMSF a b) (MkMSF c d) =
      (a * fromInteger (natToInteger d)) > (c * fromInteger (natToInteger b))

-----------------------------------------------------------------------
-- BOOLE-FRÉCHET BOUNDS (Two-Event Case)
-----------------------------------------------------------------------

||| Given P(A) = pA and P(B) = pB, compute the Boole-Fréchet bounds
||| on P(A ∧ B) using the inclusion-exclusion principle.
|||
||| Lower bound: max(0, P(A) + P(B) - 1)
||| Upper bound: min(P(A), P(B))
|||
||| These are the exact bounds Wildberger derives from the Boole-Möbius
||| polynomial by enforcing non-negativity of truth-table coefficients.
public export
booleFrechetBounds : (pA : MSetFraction) -> (pB : MSetFraction) -> ProbBounds
booleFrechetBounds pA pB =
  let -- Lower: max(0, pA + pB - 1)
      sumMinus1 = subMSF (addMSF pA pB) oneMSF
      lo = if gtProbMSF sumMinus1 zeroMSF then sumMinus1 else zeroMSF
      -- Upper: min(pA, pB)
      hi = if gtProbMSF pA pB then pB else pA
  in MkBounds lo hi
  where
    gtProbMSF : MSetFraction -> MSetFraction -> Bool
    gtProbMSF (MkMSF a b) (MkMSF c d) =
      (a * fromInteger (natToInteger d)) > (c * fromInteger (natToInteger b))

-----------------------------------------------------------------------
-- INCLUSION-EXCLUSION EXTRACTION FROM MÖBIUS COEFFICIENTS
-----------------------------------------------------------------------

||| Given a list of Möbius-inverted coefficients (from mobiusInverseZ),
||| extract the probability bounds by reading off the non-negativity
||| constraints on the truth-table weights.
|||
||| Each coefficient cᵢ multiplied by the unknown target probability P
||| must satisfy cᵢ ≥ 0.  This directly yields interval constraints.
public export
extractBoundsFromMobius : List BoxInt -> List ProbBounds
extractBoundsFromMobius [] = []
extractBoundsFromMobius coeffs =
  map toBound coeffs
  where
    toBound : BoxInt -> ProbBounds
    toBound c =
      let (MkUr val) = boxToInt c
      in if val > 0 then MkBounds zeroMSF (fromBoxInt c)
         else if val < 0 then MkBounds (fromBoxInt (negate c)) oneMSF
         else trivialBounds

-----------------------------------------------------------------------
-- GEORGE BOOLE'S LAST CHALLENGE PROBLEM
-----------------------------------------------------------------------

||| Bounding the union of three events given marginal probabilities and the joint probability.
||| Given P(A), P(B), P(C), and P(A ∧ B ∧ C), returns the bounds [lo, hi] on P(A ∨ B ∨ C).
public export
threeEventUnionBounds : (pA : MSetFraction) ->
                        (pB : MSetFraction) ->
                        (pC : MSetFraction) ->
                        (pABC : MSetFraction) ->
                        ProbBounds
threeEventUnionBounds pA pB pC pABC =
  let -- Lower bound terms: pA, pB, pC, (pA + pB + pC - pABC) / 2
      sumABC = addMSF pA (addMSF pB pC)
      sumMinusJoint = subMSF sumABC pABC
      halfSum = MkMSF sumMinusJoint.num (sumMinusJoint.den + sumMinusJoint.den)

      -- Find max of lower bounds
      lo = maxOf [pA, pB, pC, halfSum]

      -- Upper bound terms: 1, pA + pB + pC - 2 * pABC
      twoJoint = addMSF pABC pABC
      upperLimit = subMSF sumABC twoJoint

      -- Find min of upper bounds
      hi = minOf [oneMSF, upperLimit]
  in MkBounds lo hi
  where
    gtProbMSF : MSetFraction -> MSetFraction -> Bool
    gtProbMSF (MkMSF a b) (MkMSF c d) =
      (a * fromInteger (natToInteger d)) > (c * fromInteger (natToInteger b))

    maxOf : List MSetFraction -> MSetFraction
    maxOf [] = zeroMSF -- fallback
    maxOf (x :: xs) = foldl (\m, y => if gtProbMSF y m then y else m) x xs

    minOf : List MSetFraction -> MSetFraction
    minOf [] = oneMSF  -- fallback
    minOf (x :: xs) = foldl (\m, y => if gtProbMSF m y then y else m) x xs

-----------------------------------------------------------------------
-- ONGOING SEQUENCES (OnSeq integration)
-----------------------------------------------------------------------

||| The Boole-Möbius transform adapted for Byte Nat truth tables.
||| For each output row i, XOR-accumulate the weights of all rows j where i ⊆ j
||| (subset via binary encoding). Self-inverse: mobiusTransformByte² = id.
public export
mobiusTransformByte : Byte Nat -> Byte Nat
mobiusTransformByte xs =
  foldl (\acc, i =>
    let val = foldl (\accInner, j =>
                addBit accInner (if isSubsetNat i j then lookupWeight j xs else Zero))
              Zero [0..7]
    in if isOne val
       then AddM (MkSing i) One acc
       else acc
  ) ZeroM [0..7]

||| An ongoing sequence of Byte Nat truth tables.
||| Aliased directly to OnVexel Bit Nat from Math.OnSeq.OnMSet.
public export
0 OnTruthTable : Type
OnTruthTable = OnVexel Bit Nat

||| Apply the Möbius transform pointwise over an ongoing truth table sequence.
public export
mobiusTransformOnSeq : OnTruthTable -> OnTruthTable
mobiusTransformOnSeq = OnMSet.map mobiusTransformByte

||| An ongoing sequence of probability bound intervals.
public export
0 OnProbBounds : Type
OnProbBounds = OnSeq ProbBounds

||| Pointwise tightening of intervals over the sequence.
public export
tightenOnBounds : OnProbBounds -> OnProbBounds -> OnSeq (Maybe ProbBounds)
tightenOnBounds = zipWith intersectBounds

||| Pointwise Boole-Fréchet bounds on two ongoing probability sequences.
public export
booleFrechetBoundsOnSeq : OnSeq MSetFraction -> OnSeq MSetFraction -> OnProbBounds
booleFrechetBoundsOnSeq = zipWith booleFrechetBounds

||| Pointwise Möbius bounds extraction from ongoing coefficients.
public export
extractBoundsFromMobiusOnSeq : OnSeq (List BoxInt) -> OnSeq (List ProbBounds)
extractBoundsFromMobiusOnSeq = OnMSet.map extractBoundsFromMobius

||| Pointwise bounding of the union of three events.
public export
threeEventUnionBoundsOnSeq : OnSeq MSetFraction -> OnSeq MSetFraction -> OnSeq MSetFraction -> OnSeq MSetFraction -> OnProbBounds
threeEventUnionBoundsOnSeq (MkOnSeq s1 at1) (MkOnSeq s2 at2) (MkOnSeq s3 at3) (MkOnSeq s4 at4) =
  let newStart = max (max s1 s2) (max s3 s4)
  in MkOnSeq newStart (\n => threeEventUnionBounds (at1 n) (at2 n) (at3 n) (at4 n))
