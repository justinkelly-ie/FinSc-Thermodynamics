module Stage0.PreorderedMonoid

import public Stage1.Order.Preorder
import Stage0.BoxInt
import Stage1.UnixelFraction
import Stage1.Goh
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- 1. BOXINT POSET ORDERING & PROOF WITNESSES
--------------------------------------------------------------------------------

||| Proof-based preorder relation for BoxInt integer state space: natLTE (boxToNat b1) (boxToNat b2) = True.
public export
0 BoxIntPreorderPrf : BoxInt -> BoxInt -> Type
BoxIntPreorderPrf b1 b2 = natLTE (boxToNat b1) (boxToNat b2) = True

||| Monotonic BoxInt ordering implementation: x <= y in integer state space.
public export
boxIntPreorder : BoxInt -> BoxInt -> Bool
boxIntPreorder b1 b2 = natLTE (boxToNat b1) (boxToNat b2)

||| Static compiler proof witness verifying preorder reflexivity (x <= x).
public export
0 verifyPreorderReflexivity : (v : Integer) -> boxIntPreorder (MkBoxInt v) (MkBoxInt v) = True
verifyPreorderReflexivity v = natLTERefl (boxToNat (MkBoxInt v))

||| Explicit Idris 2 proof witness of preorder reflexivity for BoxInt.
public export
0 boxIntReflPrf : (b : BoxInt) -> BoxIntPreorderPrf b b
boxIntReflPrf b = natLTERefl (boxToNat b)
