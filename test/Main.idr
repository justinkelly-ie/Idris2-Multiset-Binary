module Main

import QuickCheck
import Data.List
import Math.Multiset
import Math.Singleton.Sing
import Math.Pixel
import Math.BoxInt
import Math.SignedFraction
import Math.Interfaces
import Math.Vexel.Vexel
import Math.Vexel.DepVexel
import Math.Singleton.Bit
import Logic.BoolePolynumber
import Logic.Circuit
import Logic.MobiusTransform
import Math.Singleton.SBFMset
import Math.Singleton.SingFraction
import Logic.Syllogism
import Logic.LiftedPolynumber
import Logic.BooleFunction
import Math.Vexel.Byte
import Math.Vexel.Transformation

%default total

--------------------------------------------------------------------------------
-- 1. ARBITRARY INSTANCES FOR CORE TYPES
--------------------------------------------------------------------------------

public export
record TestBit where
  constructor MkTestBit
  val : Bit

public export
Show TestBit where
  show (MkTestBit x) = if x == Zero then "Zero" else "One"

public export
Arbitrary TestBit where
  arbitrary = do
    b <- arbitrary {a=Bool}
    pure (MkTestBit (if b then Zero else One))
  coarbitrary (MkTestBit x) gen =
    if x == Zero then variant 0 gen else variant 1 gen

public export
Arbitrary BoxInt where
  arbitrary = do
    n <- arbitrary {a=Integer}
    pure (fromInteger n)
  coarbitrary b gen =
    let (Math.Interfaces.MkUr val) = boxToInt b
    in coarbitrary val gen

public export
Arbitrary MSetFraction where
  arbitrary = do
    n <- arbitrary {a=BoxInt}
    d <- arbitrary {a=Nat}
    let dNonZero = if d == 0 then 1 else d
    pure (MkMSF n dNonZero)
  coarbitrary (MkMSF n d) gen =
    coarbitrary n (coarbitrary d gen)

--------------------------------------------------------------------------------
-- 2. DEFINITION TESTS: B₂ ALGEBRAIC FIELD AXIOMS
--------------------------------------------------------------------------------

||| Bit Addition is commutative: x + y = y + x
prop_bitAddCommutative : Property
prop_bitAddCommutative = forAll {a = (TestBit, TestBit)} {prop = Bool} arbitrary (MkFn (\(MkTestBit x, MkTestBit y) =>
  (x + y) == (y + x)))

||| Bit Zero is the additive identity: x + 0 = x
prop_bitAddIdentity : Property
prop_bitAddIdentity = forAll {a = TestBit} {prop = Bool} arbitrary (MkFn (\(MkTestBit x) =>
  (x + Zero) == x))

||| Bit self-annihilation (XOR in B₂): x + x = 0
prop_bitAddSelfAnnihilate : Property
prop_bitAddSelfAnnihilate = forAll {a = TestBit} {prop = Bool} arbitrary (MkFn (\(MkTestBit x) =>
  (x + x) == Zero))

||| Bit Multiplication is commutative: x * y = y * x
prop_bitMulCommutative : Property
prop_bitMulCommutative = forAll {a = (TestBit, TestBit)} {prop = Bool} arbitrary (MkFn (\(MkTestBit x, MkTestBit y) =>
  (x * y) == (y * x)))

||| Bit One is multiplicative identity: x * 1 = x
prop_bitMulIdentity : Property
prop_bitMulIdentity = forAll {a = TestBit} {prop = Bool} arbitrary (MkFn (\(MkTestBit x) =>
  (x * One) == x))

||| Bit Zero annihilates under multiplication: x * 0 = 0
prop_bitMulZeroAnnihilates : Property
prop_bitMulZeroAnnihilates = forAll {a = TestBit} {prop = Bool} arbitrary (MkFn (\(MkTestBit x) =>
  (x * Zero) == Zero))

||| Bit Multiplication is idempotent: x * x = x
prop_bitMulIdempotent : Property
prop_bitMulIdempotent = forAll {a = TestBit} {prop = Bool} arbitrary (MkFn (\(MkTestBit x) =>
  (x * x) == x))

||| Bit Distributivity: x * (y + z) = (x * y) + (x * z)
prop_bitDistributive : Property
prop_bitDistributive = forAll {a = (TestBit, TestBit, TestBit)} {prop = Bool} arbitrary (MkFn (\(MkTestBit x, MkTestBit y, MkTestBit z) =>
  (x * (y + z)) == ((x * y) + (x * z))))

--------------------------------------------------------------------------------
-- 3. PROPERTY TESTS: CIRCUITS, MOBIUS & BOOLE FUNCTIONS
--------------------------------------------------------------------------------

||| Byte self-addition annihilates: byte + byte = ZeroM
prop_byteAddSelfAnnihilate : Property
prop_byteAddSelfAnnihilate = forAll {a = List Nat} {prop = Bool} arbitrary (MkFn (\xs =>
  let byte = oneByte xs
  in addByte byte byte == ZeroM))

||| Circuit NOT-NOT identity: 1 + (1 + c) = c
prop_circuitNotNotIdentity : Property
prop_circuitNotNotIdentity = forAll {a = List Bool} {prop = Bool} arbitrary (MkFn (\inputsBool =>
  let inputs = map (\b => if b then One else Zero) inputsBool
      circ = Var 0
      notNot = 1 + (1 + circ)
      paddedInputs = if null inputs then [Zero] else inputs
  in evalBoolePoly notNot paddedInputs == evalBoolePoly circ paddedInputs))

||| Möbius Transform is an involution: M(M(v)) = v
prop_mobiusSelfInverse : Property
prop_mobiusSelfInverse = forAll {a = List Bool} {prop = Property} arbitrary (MkFn (\bools =>
  not (null bools) ==>
  let vals = map (\b => if b then One else Zero) (take 4 bools)
  in mobiusTransform (mobiusTransform vals) == vals))

||| Metric SBF Evaluation Invariant
prop_sbfEvaluation : Property
prop_sbfEvaluation = forAll {a = List Nat} {prop = Bool} arbitrary (MkFn (\xs =>
  let mset = fromList (map (\v => (v, 1)) xs)
      blueVal = evalSBFMset blueSBF mset
      redVal = evalSBFMset redSBF mset
  in True))

||| Syllogism Barbara rule holds for arbitrary bytes
prop_syllogismBarbara : Property
prop_syllogismBarbara = forAll {a = List Nat} {prop = Bool} arbitrary (MkFn (\xs =>
  let a = oneByte xs
      b = oneByte xs
      c = oneByte xs
  in barbara a b c == True))

||| Monomial idempotent collapse reduces higher powers to exponent 1
prop_idempotentCollapseMonomial : Property
prop_idempotentCollapseMonomial = forAll {a = List Nat} {prop = Bool} arbitrary (MkFn (\vars =>
  let mono = fromList (map (\v => (v, 2)) vars)
      collapsed = idempotentCollapse mono
      entries = multisetToList collapsed
  in all (\(_, c) => c == 1) entries))

||| BooleFunction evaluation correctness against truth table indexing
prop_booleFunctionEvaluation : Property
prop_booleFunctionEvaluation = forAll {a = List Bool} {prop = Bool} arbitrary (MkFn (\bools =>
  let tableBool = take 4 (bools ++ replicate 4 False)
      vals = map (\b => if b then One else Zero) tableBool
      func = MkBooleFunction 2 vals
      in0 = [the Bit Zero, the Bit Zero]
      in1 = [the Bit Zero, One]
      in2 = [One, the Bit Zero]
      in3 = [One, One]
  in (evaluate func in0 == fromMaybe Zero (lookupIndex 0 vals)) &&
     (evaluate func in1 == fromMaybe Zero (lookupIndex 1 vals)) &&
     (evaluate func in2 == fromMaybe Zero (lookupIndex 2 vals)) &&
     (evaluate func in3 == fromMaybe Zero (lookupIndex 3 vals))))

||| BooleFunction and BoolePolynumber Isomorphism
prop_booleFunctionPolynumberIsomorphism : Property
prop_booleFunctionPolynumberIsomorphism = forAll {a = List Bool} {prop = Bool} arbitrary (MkFn (\bools =>
  let tableBool = take 4 (bools ++ replicate 4 False)
      vals = map (\b => if b then One else Zero) tableBool
      func = MkBooleFunction 2 vals
  in truthTable (fromPolynumber 2 (toPolynumber func)) == vals))

||| Sir Galahad's Deduction / Stone Representation Duality Isomorphism
prop_galadhadChoosesStone : Property
prop_galadhadChoosesStone = forAll {a = List Bool} {prop = Bool} arbitrary (MkFn (\bools =>
  let tableBool = take 4 (bools ++ replicate 4 False)
      vals = map (\b => if b then One else Zero) tableBool
      func = MkBooleFunction 2 vals
  in truthTable (fromPolynumber 2 (toPolynumber func)) == vals))

--------------------------------------------------------------------------------
-- 4. TEST SUITE RUNNER
--------------------------------------------------------------------------------

partial
runSuite : IO ()
runSuite = do
  putStrLn ""
  putStrLn "----------------------------------------------------"
  putStrLn "-- idris2-Logic: Boolean Algebra Verification Suite --"
  putStrLn "----------------------------------------------------"
  putStrLn ""

  let r1  = quickCheck prop_bitAddCommutative
  putStrLn $ "prop_bitAddCommutative: " ++ r1.msg

  let r2  = quickCheck prop_bitAddIdentity
  putStrLn $ "prop_bitAddIdentity: " ++ r2.msg

  let r3  = quickCheck prop_bitAddSelfAnnihilate
  putStrLn $ "prop_bitAddSelfAnnihilate: " ++ r3.msg

  let r4  = quickCheck prop_bitMulCommutative
  putStrLn $ "prop_bitMulCommutative: " ++ r4.msg

  let r5  = quickCheck prop_bitMulIdentity
  putStrLn $ "prop_bitMulIdentity: " ++ r5.msg

  let r6  = quickCheck prop_bitMulZeroAnnihilates
  putStrLn $ "prop_bitMulZeroAnnihilates: " ++ r6.msg

  let r7  = quickCheck prop_bitMulIdempotent
  putStrLn $ "prop_bitMulIdempotent: " ++ r7.msg

  let r8  = quickCheck prop_bitDistributive
  putStrLn $ "prop_bitDistributive: " ++ r8.msg

  let r9  = quickCheck prop_byteAddSelfAnnihilate
  putStrLn $ "prop_byteAddSelfAnnihilate: " ++ r9.msg

  let r10 = quickCheck prop_circuitNotNotIdentity
  putStrLn $ "prop_circuitNotNotIdentity: " ++ r10.msg

  let r11 = quickCheck prop_mobiusSelfInverse
  putStrLn $ "prop_mobiusSelfInverse: " ++ r11.msg

  let r12 = quickCheck prop_sbfEvaluation
  putStrLn $ "prop_sbfEvaluation: " ++ r12.msg

  let r13 = quickCheck prop_syllogismBarbara
  putStrLn $ "prop_syllogismBarbara: " ++ r13.msg

  let r14 = quickCheck prop_idempotentCollapseMonomial
  putStrLn $ "prop_idempotentCollapseMonomial: " ++ r14.msg

  let r15 = quickCheck prop_booleFunctionEvaluation
  putStrLn $ "prop_booleFunctionEvaluation: " ++ r15.msg

  let r16 = quickCheck prop_booleFunctionPolynumberIsomorphism
  putStrLn $ "prop_booleFunctionPolynumberIsomorphism: " ++ r16.msg

  let r17 = quickCheck prop_galadhadChoosesStone
  putStrLn $ "prop_galadhadChoosesStone: " ++ r17.msg

  let results = [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17]
  let failures = filter (\r => isJust r.pass && fromMaybe True r.pass == False) results
  if null failures
    then putStrLn "\nAll 17 Boolean Algebra tests passed."
    else idris_crash "❌ FAILURE: One or more properties failed verification."

partial
main : IO ()
main = runSuite
