module Logic.FunctionalProbability

import Data.List
import Math.Multiset
import Math.Singleton.Sing
import Math.Vexel.Vexel
import Math.BoxInt
import public Math.SignedFraction
import Math.Interfaces
import Logic.Bridge
import Logic.BoolePolynumber

%default total

-----------------------------------------------------------------------
-- HEHNER FUNCTIONAL PROBABILITY OVER VEXEL SPACES
-----------------------------------------------------------------------

||| Row 3 complete fraction type: pairs a multiset numerator with its total universe sum denominator.
public export
record MSetFractionVexel (v : Type) where
  constructor OverMSFSpace
  numeratorMset  : Multiset BoxInt v
  denominatorSum : BoxInt

||| Smart constructor for MSetFractionVexel.
public export
mkMSetFractionVexel : Multiset BoxInt v -> BoxInt -> MSetFractionVexel v
mkMSetFractionVexel m tot = OverMSFSpace m tot

||| Normalize a multiset into an MSetFractionVexel state space.
public export
normalize : Multiset BoxInt v -> MSetFractionVexel v
normalize m =
  let tot = foldl (\acc, (_, w) => acc + w) 0 (multisetToList m)
  in OverMSFSpace m tot

||| Extract state probability from a normalized space.
public export
stateProbability : Eq v => MSetFractionVexel v -> v -> MSetFraction
stateProbability (OverMSFSpace m den) s =
  let denVal = unwrapBox den
      absDen = Math.Interfaces.integerToNat (abs denVal)
  in if absDen == 0
     then zeroMSF
     else
       let wt = lookupWeight s m
       in MkMSF wt absDen
  where
    lookupWeight : v -> Multiset BoxInt v -> BoxInt
    lookupWeight _ ZeroM = 0
    lookupWeight x (AddM y w rest) =
      if x == y then w + lookupWeight x rest else lookupWeight x rest

||| Normalize a MSetFractionVexel into a list of states and their corresponding probabilities.
public export
normalizeFraction : MSetFractionVexel v -> List (v, MSetFraction)
normalizeFraction (OverMSFSpace m den) =
  let denVal = unwrapBox den
      absDen = Math.Interfaces.integerToNat (abs denVal)
  in if absDen == 0
     then []
     else map (\(k, v) => (k, MkMSF v absDen)) (multisetToList m)

||| Exact expectation of a payload function over a discrete multiset distribution.
public export
expectation : Eq v => (v -> BoxInt) -> MSetFractionVexel v -> MSetFraction
expectation f (OverMSFSpace m den) =
  let weightedSum = foldl (\acc, (x, w) => acc + (f x * w)) 0 (multisetToList m)
      denVal = unwrapBox den
      absDen = Math.Interfaces.integerToNat (abs denVal)
  in if absDen == 0
     then zeroMSF
     else MkMSF weightedSum absDen

||| Check whether one probability dominates another.
||| a/b > c/d ⟺ a*d > c*b (for positive denominators).
public export
gtProbability : MSetFraction -> MSetFraction -> Bool
gtProbability (MkMSF a b) (MkMSF c d) =
  (a * fromInteger (natToInteger d)) > (c * fromInteger (natToInteger b))

-----------------------------------------------------------------------
-- HEHNER CALCULATIONAL QUANTIFIERS (min / max)
-----------------------------------------------------------------------

||| Minimum weight in a Vexel state space (Hehner's ∀ replacement).
public export
minWeight : Vexel BoxInt v -> Maybe BoxInt
minWeight ZeroM = Nothing
minWeight (AddM (MkSing _) w rest) =
  case minWeight rest of
    Nothing => Just w
    Just minRest => Just (if w < minRest then w else minRest)

||| Maximum weight in a Vexel state space (Hehner's ∃ replacement).
public export
maxWeight : Vexel BoxInt v -> Maybe BoxInt
maxWeight ZeroM = Nothing
maxWeight (AddM (MkSing _) w rest) =
  case maxWeight rest of
    Nothing => Just w
    Just maxRest => Just (if w > maxRest then w else maxRest)

||| Minimum evaluation of a payload function over a domain (Hehner's ∀ quantifier).
public export
forAll : (v -> BoxInt) -> List v -> Maybe BoxInt
forAll f [] = Nothing
forAll f (x :: xs) =
  let v = f x
  in case forAll f xs of
       Nothing => Just v
       Just minRest => Just (if v < minRest then v else minRest)

||| Maximum evaluation of a payload function over a domain (Hehner's ∃ quantifier).
public export
thereExists : (v -> BoxInt) -> List v -> Maybe BoxInt
thereExists f [] = Nothing
thereExists f (x :: xs) =
  let v = f x
  in case thereExists f xs of
       Nothing => Just v
       Just maxRest => Just (if v > maxRest then v else maxRest)

-----------------------------------------------------------------------
-- DOMAIN MODELS & PARADOX VERIFICATIONS
-----------------------------------------------------------------------

public export
data Gender = Boy | Girl

public export
Eq Gender where
  Boy == Boy = True
  Girl == Girl = True
  _ == _ = False

public export
Show Gender where
  show Boy = "Boy"
  show Girl = "Girl"

public export
atLeastOneGirl : MSetFractionVexel (Gender, Gender)
atLeastOneGirl = mkMSetFractionVexel (AddM (Girl, Girl) 1 ZeroM) 3

public export
probBothGirlsGivenAtLeastOne : MSetFraction
probBothGirlsGivenAtLeastOne = stateProbability atLeastOneGirl (Girl, Girl)

public export
olderChildGirl : MSetFractionVexel (Gender, Gender)
olderChildGirl = mkMSetFractionVexel (AddM (Girl, Girl) 1 ZeroM) 2

public export
probBothGirlsGivenOlderGirl : MSetFraction
probBothGirlsGivenOlderGirl = stateProbability olderChildGirl (Girl, Girl)

public export
data Card = CardRR | CardWW | CardMR

public export
Eq Card where
  CardRR == CardRR = True
  CardWW == CardWW = True
  CardMR == CardMR = True
  _ == _ = False

public export
Show Card where
  show CardRR = "CardRR"
  show CardWW = "CardWW"
  show CardMR = "CardMR"

public export
data Side = RedSide | WhiteSide

public export
Eq Side where
  RedSide == RedSide = True
  WhiteSide == WhiteSide = True
  _ == _ = False

public export
Show Side where
  show RedSide = "Red"
  show WhiteSide = "White"

public export
observedRedSide : MSetFractionVexel (Card, Side)
observedRedSide = mkMSetFractionVexel (AddM (CardRR, RedSide) 2 ZeroM) 3

public export
probOtherSideRed : MSetFraction
probOtherSideRed = stateProbability observedRedSide (CardRR, RedSide)
