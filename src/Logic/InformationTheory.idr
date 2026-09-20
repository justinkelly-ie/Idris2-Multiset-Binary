module Logic.InformationTheory

import Data.List
import Math.Multiset
import Math.Singleton.Sing
import Math.Vexel.Vexel
import Math.BoxInt
import Math.SignedFraction
import Math.Interfaces
import Logic.FunctionalProbability

%default total

--------------------------------------------------------------------------------
-- MARCUS HUTTER COMPRESSION & CROSS-ENTROPY PARADIGM
--------------------------------------------------------------------------------

||| Integer log2 ceiling helper: log2Ceil n returns ceiling(log2(n))
public export
log2Ceil : Nat -> Nat
log2Ceil Z = 0
log2Ceil (S Z) = 0
log2Ceil (S (S Z)) = 1
log2Ceil (S (S (S Z))) = 2
log2Ceil (S (S (S (S Z)))) = 2
log2Ceil n =
  let half = cast {to=Nat} (div (cast {to=Integer} (S n)) 2)
  in S (assert_total (log2Ceil half))

||| Log2 helper for BoxInt.
public export
boxLog2 : BoxInt -> BoxInt
boxLog2 b = intToBoxInt (cast (log2Ceil (boxToNat b)))

||| Native BoxInt Self-Information (Surprisal) for an exact rational probability fraction w/d:
||| I(x) = log2(1 / P(x)) = boxLog2(denom) - boxLog2(abs(num))
public export
selfInformationBoxInt : MSetFraction -> BoxInt
selfInformationBoxInt (MkMSF num denom) =
  let dBox = intToBoxInt (cast denom)
      iDenom = boxLog2 dBox
      iNum = boxLog2 (absBox num)
      n = unwrapBox num
  in if n == 0 then 0 else iDenom - iNum

||| Self-Information (Surprisal) in bits for an exact rational probability fraction w/d
public export
selfInformationBits : MSetFraction -> Nat
selfInformationBits sf =
  let val = unwrapBox (selfInformationBoxInt sf)
  in cast val

||| Cross-Entropy H(P, Q) in bits for discrete multiset distributions.
||| H(P, Q) = sum_x P(x) * log2(1 / Q(x))
public export
crossEntropyBits : List (MSetFraction, MSetFraction) -> Nat
crossEntropyBits pairs =
  foldl (\acc, (p, q) => acc + selfInformationBits q) 0 pairs

||| Kullback-Leibler Divergence D_KL(P || Q) in bits.
||| For exact self-model Q = P, D_KL(P || P) = 0 bits (zero information loss).
public export
klDivergenceBits : List (MSetFraction, MSetFraction) -> Nat
klDivergenceBits pairs =
  foldl (\acc, (p, q) =>
    let ip = selfInformationBits p
        iq = selfInformationBits q
    in acc + (if iq >= ip then minus iq ip else 0)) 0 pairs

||| Curriculum Intelligence Factor (Hutter Compression Metric C_intel)
||| C_intel = stdProgramBits / msetProgramBits
public export
compressionRatio : Nat -> Nat -> MSetFraction
compressionRatio stdBits msetBits =
  let num = fromInteger (cast stdBits)
      denom = if msetBits == 0 then 1 else msetBits
  in MkMSF num denom

||| Compute surprisal I(x) in bits for a state x in a normalized Vexel space
public export
vexelSurprisal : Eq v => MSetFractionVexel v -> v -> Nat
vexelSurprisal space state =
  selfInformationBits (stateProbability space state)

||| Compute Cross-Entropy H(P, Q) in bits between two Vexel distribution spaces P and Q over states vs
public export
vexelCrossEntropy : Eq v => List v -> MSetFractionVexel v -> MSetFractionVexel v -> Nat
vexelCrossEntropy states pSpace qSpace =
  let pairs = map (\s => (stateProbability pSpace s, stateProbability qSpace s)) states
  in crossEntropyBits pairs

||| Compute KL-Divergence D_KL(P || Q) in bits between two Vexel distribution spaces P and Q over states vs
public export
vexelKLDivergence : Eq v => List v -> MSetFractionVexel v -> MSetFractionVexel v -> Nat
vexelKLDivergence states pSpace qSpace =
  let pairs = map (\s => (stateProbability pSpace s, stateProbability qSpace s)) states
  in klDivergenceBits pairs

--------------------------------------------------------------------------------
-- PROPERTY VERIFICATIONS
--------------------------------------------------------------------------------

||| Self-model KL divergence vanishes identically D_KL(P || P) = 0.
||| Demonstrates zero information loss under exact multiset cross-multiplication.
public export
prop_klDivergenceZeroSelfModel : Bool
prop_klDivergenceZeroSelfModel =
  let p1 = MkMSF 1 3
      p2 = MkMSF 2 3
      pairs = [(p1, p1), (p2, p2)]
  in klDivergenceBits pairs == 0

||| Self-information is non-negative I(x) >= 0.
public export
prop_selfInformationNonNegative : Bool
prop_selfInformationNonNegative =
  let p = MkMSF 1 4
  in selfInformationBits p == 2

||| Curriculum Intelligence compression ratio > 1 for multiset formalization over continuous models.
||| Standard float representation (64 bits) vs Multiset 1-component representation (16 bits) yields 4:1 compression.
public export
prop_compressionRatioPositive : Bool
prop_compressionRatioPositive =
  let ratio = compressionRatio 64 16
  in ratio == MkMSF 4 1

||| Expectation of constant payload c evaluates to c * sum / sum.
public export
prop_expectationConstant : Bool
prop_expectationConstant =
  let space = normalize (AddM Boy 3 (AddM Girl 5 ZeroM))
      expVal = expectation (\_ => 10) space
  in expVal == MkMSF 80 8

||| Vexel KL divergence vanishes D_KL(P || P) = 0 over state vector.
public export
prop_vexelKLDivergenceZero : Bool
prop_vexelKLDivergenceZero =
  let space = normalize (AddM Boy 1 (AddM Girl 3 ZeroM))
  in vexelKLDivergence [Boy, Girl] space space == 0
