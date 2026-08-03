module Logic.FunctionalProbability

import Data.List
import Math.Multiset
import Math.Singleton.Sing
import Math.BoxInt
import Math.SignedFraction
import Math.Interfaces
import Math.Singleton.Bit
import Logic.Bridge
import Math.Singleton.SingFraction
import Math.Vexel.Vexel

%default total

-----------------------------------------------------------------------
-- HEHNER FUNCTIONAL PROBABILITY (Row 3)
--
-- Eric Hehner replaces infinite quantifiers (∀, ∃) with calculational
-- min/max over closed finite spaces. Probability is not an axiom
-- but a derived normalisation:
--
--   E̅ = E · (ΣE)⁻¹
--
-- In our weight-free Vexel framework, this is computed structurally by
-- counting occurrences of active states.
-----------------------------------------------------------------------

||| Helper to lookup coordinate weights in a Vexel BoxInt.
public export
lookupWeightVexel : Eq state => state -> Vexel BoxInt state -> BoxInt
lookupWeightVexel _ ZeroM = 0
lookupWeightVexel x (AddM (MkSing y) w rest) =
  if x == y then w + lookupWeightVexel x rest else lookupWeightVexel x rest

||| Compute the total signed mass of a Vexel.
public export
totalMass : Vexel BoxInt a -> BoxInt
totalMass v = multiplicityAll v

||| Compute the total unsigned mass.
public export
totalAbsMass : Vexel BoxInt a -> BoxInt
totalAbsMass v = multiplicityAll v

||| Row 3 complete fraction type.
public export
record MSetFractionVexel (v : Type) where
  constructor OverMSFSpace
  numeratorMset  : Vexel BoxInt v
  denominatorSum : Sing TrivialBase

||| Smart constructor for MSetFractionVexel.
public export
mkMSetFractionVexel : Vexel BoxInt v -> BoxInt -> MSetFractionVexel v
mkMSetFractionVexel m tot = OverMSFSpace m (MkSing BaseAnchor)

||| Helper to count occurrences of a state in a Vexel.
public export
countOccurrences : Eq v => v -> Vexel BoxInt v -> Nat
countOccurrences x v =
  let (Math.Interfaces.MkUr val) = boxToInt (lookupWeightVexel x v)
  in cast val

||| Extract the probability of a specific state in the normalised space.
public export
stateProbability : Eq v => MSetFractionVexel v -> v -> MSetFraction
stateProbability (OverMSFSpace m den) s =
  let (Math.Interfaces.MkUr val) = boxToInt (totalMass m)
      tot = cast val
  in if tot == 0
     then zeroMSF
     else
       let wt = lookupWeightVexel s m
       in MkMSF wt tot

||| Normalize a MSetFractionVexel into a list of states and their corresponding probabilities.
public export
normalizeFraction : Eq v => MSetFractionVexel v -> List (v, MSetFraction)
normalizeFraction (OverMSFSpace m den) =
  let (Math.Interfaces.MkUr val) = boxToInt (totalMass m)
      tot = cast val
  in if tot == 0
     then []
     else go m tot
  where
    go : Vexel BoxInt v -> Nat -> List (v, MSetFraction)
    go ZeroM _ = []
    go (AddM (MkSing x) w rest) tot =
      (x, MkMSF w tot) :: go rest tot

||| Minimum weight in a Vexel.
public export
minWeight : Vexel BoxInt a -> BoxInt
minWeight ZeroM = 0
minWeight _  = 1

||| Maximum weight in a Vexel.
public export
maxWeight : Vexel BoxInt a -> BoxInt
maxWeight ZeroM = 0
maxWeight _  = 1

||| Check whether two elements have equal probability in a normalised space.
public export
eqProbability : MSetFraction -> MSetFraction -> Bool
eqProbability = eqMSF

||| Check whether one probability dominates another.
public export
gtProbability : MSetFraction -> MSetFraction -> Bool
gtProbability (MkMSF a b) (MkMSF c d) =
  (a * fromInteger (natToInteger d)) > (c * fromInteger (natToInteger b))



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
twoChildrenSpace : List (Sing (Gender, Gender))
twoChildrenSpace =
  [ MkSing (Boy, Boy)
  , MkSing (Boy, Girl)
  , MkSing (Girl, Boy)
  , MkSing (Girl, Girl)
  ]

public export
atLeastOneGirl : MSetFractionVexel (Gender, Gender)
atLeastOneGirl = mkMSetFractionVexel (AddM (MkSing (Girl, Girl)) 1 ZeroM) 3

public export
probBothGirlsGivenAtLeastOne : MSetFraction
probBothGirlsGivenAtLeastOne = stateProbability atLeastOneGirl (Girl, Girl)

public export
olderChildGirl : MSetFractionVexel (Gender, Gender)
olderChildGirl = mkMSetFractionVexel (AddM (MkSing (Girl, Girl)) 1 ZeroM) 2

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
threeCardsSpace : List (Sing (Card, Side))
threeCardsSpace =
  [ MkSing (CardRR, RedSide)
  , MkSing (CardRR, RedSide)
  , MkSing (CardWW, WhiteSide)
  , MkSing (CardWW, WhiteSide)
  , MkSing (CardMR, RedSide)
  , MkSing (CardMR, WhiteSide)
  ]

public export
observedRedSide : MSetFractionVexel (Card, Side)
observedRedSide = mkMSetFractionVexel (AddM (MkSing (CardRR, RedSide)) 2 ZeroM) 3

public export
probOtherSideRed : MSetFraction
probOtherSideRed = stateProbability observedRedSide (CardRR, RedSide)

-----------------------------------------------------------------------
-- HEHNER PROBABILITY FUNCTIONALS & EXPECTATION
-----------------------------------------------------------------------

||| Hehner's Normalization Operator ↕E = E / ∑E
||| Converts an unnormalized multiset of state weights into a normalized MSetFractionVexel space.
public export
normalize : Vexel BoxInt v -> MSetFractionVexel v
normalize v =
  let tot = totalAbsMass v
  in mkMSetFractionVexel v tot

||| Expected Value Functional E[f] = ∑ f(x) · w_x / ∑ w
||| Computes the exact weighted expectation of a payload function f over a normalized distribution space.
public export
expectation : Eq v => (v -> BoxInt) -> MSetFractionVexel v -> MSetFraction
expectation f (OverMSFSpace m den) =
  let (MkUr val) = boxToInt (totalMass m)
      tot = cast val
  in if tot == 0
     then zeroMSF
     else
       let weightedSum = sumWeighted f m
       in MkMSF weightedSum tot
  where
    sumWeighted : (v -> BoxInt) -> Vexel BoxInt v -> BoxInt
    sumWeighted _ ZeroM = 0
    sumWeighted fn (AddM (MkSing x) w rest) =
      (fn x * w) + sumWeighted fn rest
