module Logic.Circuit

import Data.List
import Math.Multiset
import Math.Singleton.Bit
import public Logic.BoolePolynumber
import Math.BoxInt
import Logic.Bridge

%default total

-----------------------------------------------------------------------
-- BOOLEAN FUNCTION / POLYNUMBER
--
-- Circuit is directly aliased to BoolePolynumber, meaning logic
-- gates mathematically evaluate natively as trivial fractional multisets
-- (Modulo 2), completely eliminating the AST tree overhead as defined 
-- by N.J. Wildberger.
-----------------------------------------------------------------------

public export
Circuit : Type
Circuit = BoolePolynumber

-----------------------------------------------------------------------
-- NUM INSTANCE (Algebraic Circuits over BoolePolynumbers)
-----------------------------------------------------------------------

public export
Num Circuit where
  (+) = addBoolePoly
  (*) = mulBoolePoly
  fromInteger 0 = zeroBoolePoly
  fromInteger 1 = oneBoolePoly
  fromInteger _ = zeroBoolePoly

-----------------------------------------------------------------------
-- VARIABLES
-----------------------------------------------------------------------

||| Create an input variable (mapped to polynomial variable index k).
public export
Var : (k : Nat) -> Circuit
Var k = varBoolePoly k

-----------------------------------------------------------------------
-- CLASSICAL LOGIC GATES AS PURE ALGEBRA (Reference)
--
-- We do not define textual legacy functions like `Not` or `Or`.
-- Instead, the pure Boolean Ring natively structures calculations:
--
--   NOT a    = 1 + a
--   OR a b   = a + b + (a * b)
--   NAND a b = 1 + (a * b)
--   NOR a b  = 1 + a + b + (a * b)
--   P → Q    = 1 + P + (P * Q)
-----------------------------------------------------------------------

-----------------------------------------------------------------------
-- SCIENCE TABLE PROGRESSION: ROW 1 → ROW 2
--
-- Maps the strict Modulo-2 BoolePolynumber logic circuit (Row 1) 
-- upward to the Lifted IntPolynumber arithmetic circuit (Row 2).
-----------------------------------------------------------------------

||| Kickstarts the physics architecture progression by lifting a pure Boole
||| Circuit out of B_2 into full integer space via the Boole-Möbius transform.
public export
liftCircuit : Circuit -> IntPolynumber
liftCircuit c = booleToIntPoly c
