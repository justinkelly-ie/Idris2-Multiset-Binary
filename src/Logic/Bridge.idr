module Logic.Bridge

import Math.Multiset
import Math.BoxInt
import Math.Singleton.Sing
import Math.Singleton.Bit
import Logic.BoolePolynumber
import Logic.MobiusTransform

%default covering

-----------------------------------------------------------------------
-- BOOLE → BOXINT BRIDGE
--
-- Row 1 (Digital Repetition) operates over Bit ∈ {0,1} (𝔽₂).
-- Row 2 (Lifted Polynumbers) operates over BoxInt ∈ ℤ.
-----------------------------------------------------------------------

||| An integer-coefficient multiset polynomial over 2D variable powers.
public export
IntPolynumber : Type
IntPolynumber = Multiset BoxInt (Nat, Nat)

||| Embed a Bit list (truth table or coefficient vector) into BoxInt list.
public export
bitsToBoxInts : List Bit -> List BoxInt
bitsToBoxInts = map bitToBoxInt

-----------------------------------------------------------------------
-- 2. LIFTING: BoolePolynumber → IntPolynumber
-----------------------------------------------------------------------

||| Lift a BoolePolynumber to IntPolynumber.
public export
booleToIntPoly : BoolePolynumber -> IntPolynumber
booleToIntPoly ZeroM = ZeroM
booleToIntPoly (AddM k v rest) =
  if isZero v then booleToIntPoly rest
  else AddM (k, Z) 1 (booleToIntPoly rest)
