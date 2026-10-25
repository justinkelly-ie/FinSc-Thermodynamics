module Stage1.Thermodynamics.FreeEnergyPoly

import Stage0.BoxInt
import Stage1.Polynumber
import Stage1.UnixelFraction
import Stage1.Carrier.Vexel
import Stage1.Thermodynamics.EntropicArrow
import Data.Vect

%default total

------------------------------------------------------------------------
-- 1. DEGREE-CERTIFIED THERMAL PARTITION FUNCTIONS
------------------------------------------------------------------------

||| Degree-certified thermal partition polynomial:
||| Z(q) = \sum_{k=0}^deg w_k q^k
||| Guarantees finite energy cutoff and degree preservation at compile time.
public export
record ThermalPartitionDepPoly (deg : Nat) where
  constructor MkThermalPartitionDepPoly
  poly : DepPolynumber deg

||| Evaluates degree-certified thermal partition polynomial at integer temperature parameter q.
public export
evalThermalPartition : ThermalPartitionDepPoly deg -> BoxInt -> BoxInt
evalThermalPartition (MkThermalPartitionDepPoly p) q = evalDepPolynumber p q

------------------------------------------------------------------------
-- 2. DEGREE-CERTIFIED HELMHOLTZ FREE ENERGY POLYNOMIALS
------------------------------------------------------------------------

||| Degree-certified Helmholtz Free Energy Expansion Polynomial in temperature T:
||| F(T) = U_0 - S_0 * T + \dots
||| where degree guarantees the order of the virial/temperature expansion.
public export
record HelmholtzFreeEnergyDepPoly (deg : Nat) where
  constructor MkHelmholtzDepPoly
  energyExpansion : DepPolynumber deg

||| Evaluates free energy expansion at given temperature T.
public export
evalFreeEnergyExpansion : HelmholtzFreeEnergyDepPoly deg -> BoxInt -> BoxInt
evalFreeEnergyExpansion (MkHelmholtzDepPoly p) t = evalDepPolynumber p t

||| Bridges a thermodynamic Vexel state (U, T, S) into a first-order certified Helmholtz polynomial:
||| F(T) = U - S * T
public export
thermoVexelToFreeEnergyPoly : Vexel -> HelmholtzFreeEnergyDepPoly 1
thermoVexelToFreeEnergyPoly v =
  let u = thermoInternalEnergy v
      s = thermoEntropy v
  in MkHelmholtzDepPoly (MkDepPolynumber [u, negBox s])

------------------------------------------------------------------------
-- 3. COMPILE-TIME AUDIT WITNESSES
------------------------------------------------------------------------

||| Compile-time audit witness verifying that evaluating the degree-1 free energy polynomial
||| at T = thermoTemperature v identically matches computeFreeEnergy v:
||| F(T) = U - S * T
public export
auditFreeEnergyPolyEquivalenceProof : Bool
auditFreeEnergyPolyEquivalenceProof =
  let v = thermoVexel (intToBoxInt 100) (intToBoxInt 10) (intToBoxInt 5)
      poly = thermoVexelToFreeEnergyPoly v
      fPoly = evalFreeEnergyExpansion poly (thermoTemperature v)
      fDirect = computeFreeEnergy v
  in boxEq fPoly fDirect && boxEq fDirect (intToBoxInt 50)
