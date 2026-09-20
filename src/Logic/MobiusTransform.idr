module Logic.MobiusTransform

import Data.List
import Data.Nat
import Math.Multiset
import Math.BoxInt
import Math.Interfaces
import Math.Singleton.Sing
import Math.Singleton.Bit
import Math.Vexel.Byte
import Math.OnSeq.OnMSet
import public Math.SignedFraction
import Logic.BoolePolynumber

%default covering

||| Computes the Boole-Möbius transform over a truth table list of Bit values.
||| T(i,j) = 1 iff i ⊆ j (subset inclusion via binary encoding). Self-inverse: T² = I.
public export
mobiusTransform : List Bit -> List Bit
mobiusTransform [] = []
mobiusTransform table =
  let n = length table
      indices = range Z n
  in map (\i => foldl addBit Zero (map (\j => if isSubsetNat i j then getAt j table else Zero) indices)) indices
  where
    range : Nat -> Nat -> List Nat
    range k Z = []
    range k (S m) = k :: range (S k) m
    
    getAt : Nat -> List Bit -> Bit
    getAt Z (x :: _) = x
    getAt (S k) (_ :: xs) = getAt k xs
    getAt _ [] = Zero

-----------------------------------------------------------------------
-- PROBABILITY BOUNDS (HAILPERIN / BOOLE)
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

||| The trivial bounds [0/1, 1/1] — no information.
public export
trivialBounds : ProbBounds
trivialBounds = MkBounds zeroMSF oneMSF

||| An exact probability (degenerate interval where lo == hi).
public export
exactBounds : MSetFraction -> ProbBounds
exactBounds p = MkBounds p p

-----------------------------------------------------------------------
-- BOOLE-FRÉCHET & BOOLE'S LAST CHALLENGE BOUNDS
-----------------------------------------------------------------------

||| Given P(A) = pA and P(B) = pB, compute the Boole-Fréchet bounds
||| on P(A ∧ B) using the inclusion-exclusion principle.
public export
booleFrechetBounds : (pA : MSetFraction) -> (pB : MSetFraction) -> ProbBounds
booleFrechetBounds pA pB =
  let sumMinus1 = subMSF (addMSF pA pB) oneMSF
      lo = if gtProbMSF sumMinus1 zeroMSF then sumMinus1 else zeroMSF
      hi = if gtProbMSF pA pB then pB else pA
  in MkBounds lo hi
  where
    gtProbMSF : MSetFraction -> MSetFraction -> Bool
    gtProbMSF (MkMSF a b) (MkMSF c d) =
      (a * fromInteger (natToInteger d)) > (c * fromInteger (natToInteger b))

||| Bounding the union of three events given marginal probabilities and the joint probability.
||| Given P(A), P(B), P(C), and P(A ∧ B ∧ C), returns the bounds [lo, hi] on P(A ∨ B ∨ C).
public export
threeEventUnionBounds : (pA : MSetFraction) ->
                        (pB : MSetFraction) ->
                        (pC : MSetFraction) ->
                        (pABC : MSetFraction) ->
                        ProbBounds
threeEventUnionBounds pA pB pC pABC =
  let sumABC = addMSF pA (addMSF pB pC)
      sumMinusJoint = subMSF sumABC pABC
      halfSum = MkMSF sumMinusJoint.num (sumMinusJoint.den + sumMinusJoint.den)
      lo = maxOf [pA, pB, pC, halfSum]
      twoJoint = addMSF pABC pABC
      upperLimit = subMSF sumABC twoJoint
      hi = minOf [oneMSF, upperLimit]
  in MkBounds lo hi
  where
    gtProbMSF : MSetFraction -> MSetFraction -> Bool
    gtProbMSF (MkMSF a b) (MkMSF c d) =
      (a * fromInteger (natToInteger d)) > (c * fromInteger (natToInteger b))

    maxOf : List MSetFraction -> MSetFraction
    maxOf [] = zeroMSF
    maxOf (x :: xs) = foldl (\m, y => if gtProbMSF y m then y else m) x xs

    minOf : List MSetFraction -> MSetFraction
    minOf [] = oneMSF
    minOf (x :: xs) = foldl (\m, y => if gtProbMSF m y then y else m) x xs

-----------------------------------------------------------------------
-- INTEGER-VALUED BOOLE-MÖBIUS TRANSFORM OVER BoxInt (ℤ)
-----------------------------------------------------------------------

||| Count the number of set bits in a Nat (population count).
public export
popCount : Nat -> Nat
popCount Z = Z
popCount n =
  let low = if isOdd n then 1 else 0
  in low + popCount (assert_smaller n (half n))

||| Check if a Nat is even via structural recursion.
public export
evenNat : Nat -> Bool
evenNat Z = True
evenNat (S Z) = False
evenNat (S (S k)) = evenNat k

||| Forward integer Boole-Möbius transform.
public export
mobiusTransformZ : List BoxInt -> List BoxInt
mobiusTransformZ xs =
  let size = length xs
  in map (\i => foldRowZ i 0 xs) [0 .. minus size 1]
  where
    foldRowZ : Nat -> Nat -> List BoxInt -> BoxInt
    foldRowZ _ _ [] = 0
    foldRowZ i j (x :: rest) =
      let contrib = if isSubsetNat i j then x else 0
      in contrib + foldRowZ i (S j) rest

||| Inverse integer Boole-Möbius transform (Möbius inversion).
public export
mobiusInverseZ : List BoxInt -> List BoxInt
mobiusInverseZ ys =
  let size = length ys
  in map (\i => foldInvRowZ i 0 ys) [0 .. minus size 1]
  where
    foldInvRowZ : Nat -> Nat -> List BoxInt -> BoxInt
    foldInvRowZ _ _ [] = 0
    foldInvRowZ i j (y :: rest) =
      if isSubsetNat i j
      then let diffBits = popCount j `minus` popCount i
               sign = if evenNat diffBits then 1 else (-1)
           in (sign * y) + foldInvRowZ i (S j) rest
      else foldInvRowZ i (S j) rest

-----------------------------------------------------------------------
-- ONGOING SEQUENCES (OnSeq integration)
-----------------------------------------------------------------------

||| Apply the Boole-Möbius transform to a Byte Nat truth table.
public export
mobiusTransformByte : Byte Nat -> Byte Nat
mobiusTransformByte b =
  let plainMset = mapMultiset fromSing b
      dense = sparseToDense 8 plainMset
      transformed = mobiusTransform dense
  in mapMultiset toSing (denseToSparse transformed)

||| An ongoing sequence of Byte Nat truth tables.
public export
0 OnTruthTable : Type
OnTruthTable = OnSeq (Byte Nat)

||| Apply the Möbius transform pointwise over an ongoing truth table sequence.
public export
mobiusTransformOnSeq : OnTruthTable -> OnTruthTable
mobiusTransformOnSeq = Math.OnSeq.OnMSet.map mobiusTransformByte
