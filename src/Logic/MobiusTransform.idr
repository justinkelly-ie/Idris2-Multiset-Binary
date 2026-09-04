module Logic.MobiusTransform

import Data.List
import Data.Nat
import Math.Multiset
import Math.BoxInt
import Core.BoxInt as CBox
import Math.Interfaces
import Math.Singleton.Sing
import Math.Singleton.Bit
import Logic.BoolePolynumber
import Core.UnixelFraction

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

||| Rational probability fraction alias to UnixelFraction from Idris2-Multiset-Transform.
public export
0 MSetFraction : Type
MSetFraction = UnixelFraction

||| Is subset predicate for Nat binary encodings.
public export
isSubsetNat : Nat -> Nat -> Bool
isSubsetNat i j = (i == (i `land` j))
  where
    land : Nat -> Nat -> Nat
    land Z _ = Z
    land _ Z = Z
    land a b = case (a `mod` 2, b `mod` 2) of
                 (S Z, S Z) => S (2 * land (a `div` 2) (b `div` 2))
                 _         => 2 * land (a `div` 2) (b `div` 2)

-----------------------------------------------------------------------
-- PROBABILITY BOUNDS (HAILPERIN / BOOLE)
-----------------------------------------------------------------------

||| A closed interval [lo, hi] of UnixelFractions.
||| Represents the tightest possible bounds on an unknown probability.
public export
record ProbBounds where
  constructor MkBounds
  lo : UnixelFraction
  hi : UnixelFraction

public export
Show ProbBounds where
  show (MkBounds l h) = "[" ++ show l ++ ", " ++ show h ++ "]"

public export
Eq ProbBounds where
  (MkBounds l1 h1) == (MkBounds l2 h2) = l1 == l2 && h1 == h2

||| The trivial bounds [0/1, 1/1] — no information.
public export
trivialBounds : ProbBounds
trivialBounds = MkBounds (mkUnixelFraction (CBox.intToBoxInt 0) 1) (mkUnixelFraction (CBox.intToBoxInt 1) 1)

||| An exact probability (degenerate interval where lo == hi).
public export
exactBounds : UnixelFraction -> ProbBounds
exactBounds p = MkBounds p p
