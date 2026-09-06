module Logic.BoolePolynumber

import Data.List
import Data.Nat
import Math.Multiset
import public Math.Singleton.Bit
import Math.BoxInt

%default covering

-----------------------------------------------------------------------
-- BOOLE POLYNUMBERS AS MULTISETS
--
-- Source: Wildberger Lectures 264, 267.
--
-- A Boole polynumber = Multiset Bit Nat
--   Element: subset index (Nat, binary-encoded variable set)
--   Count:   coefficient (Bit, in B₂)
--
-- Addition is addMultiset + annihilateMultiset.
-- Since One + One = Zero, duplicate terms cancel (XOR).
--
-- Mirrors BoxInt = Multiset Integer SignedUnit.
-----------------------------------------------------------------------

||| A Boole polynumber: a multiset of subset indices with Bit counts.
||| Entry (k, One) represents the term for subset k.
||| Index 0 = constant term 1.
||| Index k: bit j set ⟺ variable aⱼ in the term.
public export
BoolePolynumber : Type
BoolePolynumber = Multiset Bit Nat

||| A Boolean function (truth table) as a multiset.
public export
BooleanFunction : Type
BooleanFunction = Multiset Bit Nat

-----------------------------------------------------------------------
-- BITWISE NAT OPERATIONS (structural recursion)
-----------------------------------------------------------------------

||| Test whether the lowest bit is set.
public export
isOdd : Nat -> Bool
isOdd Z = False
isOdd (S Z) = True
isOdd (S (S k)) = isOdd k

||| Division by 2 via structural recursion.
public export
half : Nat -> Nat
half Z = Z
half (S Z) = Z
half (S (S k)) = S (half k)

||| Subset inclusion: i ⊆ j iff every bit set in i is set in j.
public export
isSubsetNat : Nat -> Nat -> Bool
isSubsetNat Z _ = True
isSubsetNat (S _) Z = False
isSubsetNat i j =
  if isOdd i && not (isOdd j)
  then False
  else isSubsetNat (assert_smaller i (half i)) (assert_smaller j (half j))

||| Bitwise OR on Nat.
public export
bitOrNat : Nat -> Nat -> Nat
bitOrNat Z j = j
bitOrNat i Z = i
bitOrNat i j =
  let low = if isOdd i || isOdd j then 1 else 0
  in low + 2 * bitOrNat (assert_smaller i (half i)) (assert_smaller j (half j))

-----------------------------------------------------------------------
-- CONSTRUCTION
-----------------------------------------------------------------------

||| The zero Boole polynumber.
public export
zeroBoolePoly : BoolePolynumber
zeroBoolePoly = ZeroM

||| The constant-one polynumber (subset index 0 = constant term).
public export
oneBoolePoly : BoolePolynumber
oneBoolePoly = AddM 0 One ZeroM

||| A single-variable polynumber aₖ (subset index = 2^k).
public export
varBoolePoly : (k : Nat) -> BoolePolynumber
varBoolePoly k = AddM (power 2 k) One ZeroM

||| A single term with a given subset index.
public export
termBoolePoly : (subsetIndex : Nat) -> BoolePolynumber
termBoolePoly idx = AddM idx One ZeroM

-----------------------------------------------------------------------
-- ARITHMETIC
-----------------------------------------------------------------------

||| Addition: lazy concatenation + annihilation.
||| One + One = Zero in Bit, so duplicates cancel (XOR).
public export
addBoolePoly : BoolePolynumber -> BoolePolynumber -> BoolePolynumber
addBoolePoly p q = annihilateMultiset (addMultiset p q)

||| Multiplication: aₖ · aₗ = a_{k|l} (bitwise OR).
||| Because x² = x in B₂.
public export
mulBoolePoly : BoolePolynumber -> BoolePolynumber -> BoolePolynumber
mulBoolePoly ZeroM _ = ZeroM
mulBoolePoly (AddM ki ci rest) ys =
  addBoolePoly (mulInner ki ci ys) (mulBoolePoly rest ys)
  where
    mulInner : Nat -> Bit -> BoolePolynumber -> BoolePolynumber
    mulInner _ _ ZeroM = ZeroM
    mulInner ki ci (AddM kj cj rest) =
      let prodIdx = bitOrNat ki kj
          prodCoeff = mulBit ci cj
      in insertItem prodIdx prodCoeff (mulInner ki ci rest)

-----------------------------------------------------------------------
-- CONVERSION: DENSE ↔ SPARSE
-----------------------------------------------------------------------

||| Dense truth table to sparse multiset.
public export
denseToSparse : List Bit -> Multiset Bit Nat
denseToSparse = go 0
  where
    go : Nat -> List Bit -> Multiset Bit Nat
    go _ [] = ZeroM
    go idx (x :: rest) =
      if isOne x
        then AddM idx One (go (S idx) rest)
        else go (S idx) rest

||| Sparse multiset to dense list.
public export
sparseToDense : (size : Nat) -> Multiset Bit Nat -> List Bit
sparseToDense size m = map (\idx => lookupBVal idx m) [0 .. minus size 1]
  where
    lookupBVal : Nat -> Multiset Bit Nat -> Bit
    lookupBVal _ ZeroM = Zero
    lookupBVal idx (AddM k v rest) =
      if k == idx then addBit v (lookupBVal idx rest)
      else lookupBVal idx rest

-----------------------------------------------------------------------
-- EVALUATION
-----------------------------------------------------------------------

||| Evaluate a term at an input assignment.
public export
evalTerm : Nat -> List Bit -> Bit
evalTerm Z _ = One
evalTerm k inputs = go k inputs
  where
    go : Nat -> List Bit -> Bit
    go Z _ = One
    go _ [] = One
    go k (v :: vs) =
      let thisVal = if isOdd k then v else One
      in mulBit thisVal (go (assert_smaller k (half k)) vs)

||| Evaluate a Boole polynumber at a point.
public export
evalBoolePoly : BoolePolynumber -> List Bit -> Bit
evalBoolePoly ZeroM _ = Zero
evalBoolePoly (AddM k c rest) inputs =
  addBit (mulBit c (evalTerm k inputs)) (evalBoolePoly rest inputs)

-----------------------------------------------------------------------
-- EQUIVALENCE
-----------------------------------------------------------------------

||| Two polynumbers are equivalent iff their sum annihilates to zero.
public export
polyEquiv : BoolePolynumber -> BoolePolynumber -> Bool
polyEquiv p q = annihilateMultiset (addMultiset p q) == ZeroM

||| Two polynumbers are equivalent iff their sum annihilates to zero (returning Bit).
public export
polyEquivBit : BoolePolynumber -> BoolePolynumber -> Bit
polyEquivBit p q =
  if annihilateMultiset (addMultiset p q) == ZeroM then One else Zero

-----------------------------------------------------------------------
-- DISPLAY
-----------------------------------------------------------------------

export
showTerm : Nat -> String
showTerm Z = "1"
showTerm k = go 0 k
  where
    go : Nat -> Nat -> String
    go _ Z = ""
    go pos k =
      let this = if isOdd k then "a" ++ show pos else ""
      in this ++ go (S pos) (assert_smaller k (half k))

export
showBoolePoly : BoolePolynumber -> String
showBoolePoly ZeroM = "0"
showBoolePoly p =
  let str = go p
  in if str == "" then "0" else str
  where
    go : BoolePolynumber -> String
    go ZeroM = ""
    go (AddM k v rest) =
      if isOne v
        then let tail = go rest
             in if tail == "" then showTerm k else showTerm k ++ " + " ++ tail
        else go rest
