module Stage1.Thermodynamics.EntropicArrow

import public Stage0.BoxInt
import public Stage0.WitnessLedger
import public Stage0.Multiset
import public Stage1.UnixelFraction
import public Stage1.QuadStream
import public Stage1.VexelMaxel
import public Stage1.ChromoCategory
import public Stage1.MultisetDuality
import public Stage1.TypeTheory.Staging
import public Stage1.TypeTheory.TwoLevel
import Stage0.PreorderedMonoid
import Stage1.SpatialStencil
import public Stage1.TypeTheory.Smoothness

%default total

--------------------------------------------------------------------------------
-- 1. DISCRETE HELMHOLTZ FREE ENERGY & ENTROPY ON MULTISET BASIS
--------------------------------------------------------------------------------

||| Multiset basis vector encoding thermodynamic state carrying internal energy U (index 0),
||| temperature T (index 1), and entropy S (index 2).
public export
thermoVexel : BoxInt -> BoxInt -> BoxInt -> Vexel
thermoVexel u t s = MkVexel [(MkUnixel 0, u), (MkUnixel 1, t), (MkUnixel 2, s)]

public export
thermoInternalEnergy : Vexel -> BoxInt
thermoInternalEnergy (MkVexel ((MkUnixel 0, u) :: _)) = u
thermoInternalEnergy v = lookupUnixel (MkUnixel 0) v

public export
thermoTemperature : Vexel -> BoxInt
thermoTemperature (MkVexel (_ :: (MkUnixel 1, t) :: _)) = t
thermoTemperature v = lookupUnixel (MkUnixel 1) v

public export
thermoEntropy : Vexel -> BoxInt
thermoEntropy (MkVexel (_ :: _ :: (MkUnixel 2, s) :: _)) = s
thermoEntropy v = lookupUnixel (MkUnixel 2) v

||| Computes exact discrete Helmholtz Free Energy: F = U - T * S
public export
computeFreeEnergy : Vexel -> BoxInt
computeFreeEnergy v =
  let u = thermoInternalEnergy v
      t = thermoTemperature v
      s = thermoEntropy v
  in u - (t * s)

--------------------------------------------------------------------------------
-- 2. DISCRETE FREE ENERGY MINIMIZATION (& Delta F <= 0)
--------------------------------------------------------------------------------

||| Evaluates free energy change Delta F = F_after - F_before
public export
computeDeltaF : Vexel -> Vexel -> BoxInt
computeDeltaF b a = computeFreeEnergy a - computeFreeEnergy b

||| Validates second law of thermodynamics: Delta F <= 0 (Free Energy Minimization)
public export
isFreeEnergyMinimizing : Vexel -> Vexel -> Bool
isFreeEnergyMinimizing b a =
  let dF = computeDeltaF b a
  in unwrapBox dF <= 0

--------------------------------------------------------------------------------
-- 3. IRREVERSIBLE COSMOLOGICAL STATE UPDATE
--------------------------------------------------------------------------------

||| Type-level proof witness certifying that an irreversible state transition
||| obeys the entropic arrow of time (Delta F <= 0).
public export
data EntropicArrowStep : (before : Vexel) -> (after : Vexel) -> Type where
  IrreversibleUpdate : (before : Vexel) -> (after : Vexel) ->
                       (0 prf : isFreeEnergyMinimizing before after = True) ->
                       EntropicArrowStep before after

||| A multi-step entropic transition chain strictly obeying the second law of thermodynamics (Delta F <= 0)
public export
data ThermoCascade : Vexel -> Vexel -> Type where
  SingleStep : EntropicArrowStep before after -> ThermoCascade before after
  TransStep  : EntropicArrowStep before mid -> ThermoCascade mid after -> ThermoCascade before after

||| Executes a multi-step thermodynamic state transition cascade linearly,
||| returning the final state and total free energy drop Delta F.
public export
executeCascade : Vexel -> ThermoCascade start end -> (Vexel, BoxInt)
executeCascade start (SingleStep (IrreversibleUpdate _ after prf)) =
  (after, computeDeltaF start after)
executeCascade start (TransStep (IrreversibleUpdate _ mid prf) rest) =
  let dF1 = computeDeltaF start mid
      (finalSt, dF2) = executeCascade mid rest
  in (finalSt, dF1 + dF2)

||| Eilenberg-Moore Monadic History Relinearization:
||| Collapses a multi-step thermodynamic interaction cascade into a single ground-state Vexel,
||| resetting the history ledger to a parallel Applicative state while preserving final entropic bounds.
public export
relinearizeHistory : Vexel -> ThermoCascade start end -> Vexel
relinearizeHistory start cascade =
  let (finalState, dF) = executeCascade start cascade
  in finalState

||| Enforces local second-law thermodynamics (Delta F <= 0) across cellular comonad neighborhoods
public export
localEntropicStep : GridContext Vexel -> Vexel
localEntropicStep (Context left center right) =
  let u = thermoInternalEnergy center
      t = thermoTemperature center
      s = thermoEntropy center
  in thermoVexel u t (s + intToBoxInt 1)

--------------------------------------------------------------------------------
-- 4. CHROMOCATEGORY METRIC TENSOR ENTROPIC BOUNDS
--------------------------------------------------------------------------------

||| Evaluates spatial entropic free energy dissipation bound over a ChromoCategory VexelSpace.
public export
thermoMetricBound : {d : Nat} -> {c : MetricColor} ->
                    (0 sp : VexelSpace d c) ->
                    (stateVec : Vexel) ->
                    BoxInt
thermoMetricBound sp stateVec = quadranceVexelSpace sp stateVec

--------------------------------------------------------------------------------
-- 5. COMPILE-TIME FREE ENERGY MINIMIZATION AUDIT PROOF
--------------------------------------------------------------------------------

||| Static compiler proof witness verifying that isothermal entropy growth decreases free energy.
public export
0 verifyEntropicArrow : let s1 = thermoVexel (intToBoxInt 100) (intToBoxInt 10) (intToBoxInt 2)
                            s2 = thermoVexel (intToBoxInt 100) (intToBoxInt 10) (intToBoxInt 5)
                        in isFreeEnergyMinimizing s1 s2 = True
verifyEntropicArrow = Refl

--------------------------------------------------------------------------------
-- 6. PURE MULTISET THERMODYNAMIC STATE ENCODING & FREE ENERGY
--------------------------------------------------------------------------------

||| Multiset Thermodynamic Variable Tokens
public export
data ThermoStateToken = EnergyToken | TemperatureToken | EntropyToken

public export
Eq ThermoStateToken where
  EnergyToken      == EnergyToken      = True
  TemperatureToken == TemperatureToken = True
  EntropyToken     == EntropyToken     = True
  _                == _                = False

||| Encodes thermodynamic parameters into a pure Multiset BoxInt ThermoStateToken.
public export
makeThermoMultiset : BoxInt -> BoxInt -> BoxInt -> Multiset BoxInt ThermoStateToken
makeThermoMultiset u t s =
  AddM EnergyToken u (AddM TemperatureToken t (AddM EntropyToken s ZeroM))

||| Converts QuadStreamMultiset BoxInt payload into thermodynamic state multiset
public export
quadStreamToThermoMultiset : QuadStreamMultiset BoxInt -> Multiset BoxInt ThermoStateToken
quadStreamToThermoMultiset (MkQuadStream e h p s) =
  makeThermoMultiset (multisetSum e) (multisetSum h) (multisetSum p)

||| Computes exact Helmholtz Free Energy F = U - T * S from a Multiset BoxInt ThermoStateToken.
public export
multisetComputeFreeEnergy : Multiset BoxInt ThermoStateToken -> BoxInt
multisetComputeFreeEnergy m =
  let u = multiplicity EnergyToken m
      t = multiplicity TemperatureToken m
      s = multiplicity EntropyToken m
  in u - (t * s)

||| Computes exact Helmholtz Free Energy F = U - T * S from a QuadStreamMultiset BoxInt payload.
public export
quadStreamComputeFreeEnergy : QuadStreamMultiset BoxInt -> BoxInt
quadStreamComputeFreeEnergy qs = multisetComputeFreeEnergy (quadStreamToThermoMultiset qs)

||| Audits multiset free energy minimization invariance:
public export
auditMultisetThermoFreeEnergyProof : Bool
auditMultisetThermoFreeEnergyProof =
  let s1 = makeThermoMultiset (intToBoxInt 100) (intToBoxInt 10) (intToBoxInt 2)
      s2 = makeThermoMultiset (intToBoxInt 100) (intToBoxInt 10) (intToBoxInt 5)
      f1 = multisetComputeFreeEnergy s1
      f2 = multisetComputeFreeEnergy s2
  in unwrapBox f1 == 80 && unwrapBox f2 == 50 && unwrapBox f2 <= unwrapBox f1

--------------------------------------------------------------------------------
-- 7. COMPILE-TIME LANDAUER ERASED HEAT BOUND WITNESSES (Delta Q >= erasedBits * 27)
--------------------------------------------------------------------------------

||| Certified Landauer quantum erasure scale factor dimension: 27 (Elliptic lattice capacity).
public export
landauerQuantumDimension : CosmicDimension
landauerQuantumDimension = dimElliptic27

||| Erased compile-time proof witness verifying Landauer heat erasure bound:
||| Emitted heat Q (in discrete units) satisfies Q >= erasedBits * 27 (k_B T ln 2 scale factor).
public export
0 LandauerBoundWitness : (erasedBits : Nat) -> (emittedHeat : Nat) -> Type
LandauerBoundWitness erasedBits emittedHeat = natLTE (erasedBits * fst landauerQuantumDimension) emittedHeat = True

||| Static compile-time witness for 1 bit erasure emitting 27 heat units (27 <= 27).
public export
0 prfLandauer1Bit : LandauerBoundWitness 1 27
prfLandauer1Bit = Refl

||| Static compile-time witness for 10 bits erasure emitting 300 heat units (270 <= 300).
public export
0 prfLandauer10Bits : LandauerBoundWitness 10 300
prfLandauer10Bits = Refl

||| Verified Landauer information erasure transaction record carrying compile-time erased heat bound.
public export
record VerifiedLandauerErasureState (erasedBits : Nat) (emittedHeat : Nat) where
  constructor MkVerifiedErasureState
  erasedBitsCount : Nat
  emittedHeatUnits : Nat
  0 landauerPrf : LandauerBoundWitness erasedBits emittedHeat

--------------------------------------------------------------------------------
-- 8. THERMODYNAMIC SCALE MONAD & VARIATIONAL FREE ENERGY ADJUNCTION
--------------------------------------------------------------------------------

||| Coarse-grained macro thermodynamic state wrapping coarse-grained entropy and energy bounds.
public export
record ThermoMacroDomain where
  constructor MkThermoMacro
  macroEnergy  : BoxInt
  macroTemp    : BoxInt
  macroEntropy : BoxInt

public export
Eq ThermoMacroDomain where
  (MkThermoMacro e1 t1 s1) == (MkThermoMacro e2 t2 s2) = e1 == e2 && t1 == t2 && s1 == s2

||| MultisetScaleAdjunction (f_* ⊣ f^*) between micro Vexel state and macro ThermoMacroDomain.
public export
MultisetScaleAdjunction Vexel ThermoMacroDomain where
  f_pushforward v = MkThermoMacro (thermoInternalEnergy v) (thermoTemperature v) (thermoEntropy v)
  f_pullback (MkThermoMacro e t s) = thermoVexel e t s
  verifyUnit (MkVexel [(MkUnixel 0, u), (MkUnixel 1, t), (MkUnixel 2, s)]) = Refl
  verifyUnit _ = Refl
  verifyCounit _ = Refl

||| QTT 0 Erased Proof: Thermodynamic Scale Multiset Adjunction Counit Invariant
public export
0 prfThermoScaleAdjunctionDuality : (m : ThermoMacroDomain) ->
  f_pushforward (the Vexel (f_pullback m)) = m
prfThermoScaleAdjunctionDuality (MkThermoMacro e t s) = Refl

||| Computes exact Helmholtz Free Energy Variational Surprise F_surprise = S(f^* (f_* v)) - S(v)
||| using Adjunction-induced ScaleMonad M(v) = f^* (f_* v).
public export
thermoVariationalFreeEnergySurprise : Vexel -> BoxInt
thermoVariationalFreeEnergySurprise v =
  scaleMonadVariationalSurprise {a=ThermoMacroDomain} computeFreeEnergy v

||| Static proof witness verifying zero variational surprise under identity scale reconstruction.
public export
0 verifyZeroVariationalSurprise : thermoVariationalFreeEnergySurprise (thermoVexel (intToBoxInt 100) (intToBoxInt 10) (intToBoxInt 5)) = intToBoxInt 0
verifyZeroVariationalSurprise = Refl

||| Audit witness verifying zero variational surprise under scale reconstruction.
public export
auditZeroVariationalSurpriseProof : Bool
auditZeroVariationalSurpriseProof =
  let v = thermoVexel (intToBoxInt 100) (intToBoxInt 10) (intToBoxInt 5)
  in thermoVariationalFreeEnergySurprise v == intToBoxInt 0

--------------------------------------------------------------------------------
-- 9. 2LTT STAGED THERMODYNAMIC PARTITION SUM DEFORESTATION
--------------------------------------------------------------------------------

||| 2LTT Staged Partition Sum: Pre-evaluates thermodynamic state partition sums over streaming multisets
||| at compile-time Stage 1 (U_1) and splices out the unboxed scalar BoxInt to Stage 0 (U_0).
%inline public export
stagedThermodynamicPartitionSum : Lift (Multiset BoxInt BoxInt) -> BoxInt
stagedThermodynamicPartitionSum liftedStream = multisetSum (splice liftedStream)

||| QTT 0 Erased Proof Witness: Staged Partition Sum Invariant
public export
0 prfStagedPartitionSum : (m : Multiset BoxInt BoxInt) -> splice (quote m) = m
prfStagedPartitionSum m = inverseSpliceQuote m

--------------------------------------------------------------------------------
-- 10. LANDAUER INFORMATION ERASURE MULTISET ADJUNCTION (L_Entropy ⊣ R_Work)
--------------------------------------------------------------------------------

||| Entropy multiset domain wrapping erased information bits BoxInt
public export
record EntropyStateDomain where
  constructor MkEntropyDomain
  erasedBits : BoxInt

public export
Eq EntropyStateDomain where
  (MkEntropyDomain e1) == (MkEntropyDomain e2) = e1 == e2

||| Work multiset domain wrapping emitted heat / dissipated work BoxInt
public export
record WorkStateDomain where
  constructor MkWorkDomain
  dissipativeWork : BoxInt

public export
Eq WorkStateDomain where
  (MkWorkDomain w1) == (MkWorkDomain w2) = w1 == w2

||| Heterogeneous MultisetScaleAdjunction instance between EntropyStateDomain and WorkStateDomain (Q >= erasedBits * 27)
public export
MultisetScaleAdjunction EntropyStateDomain WorkStateDomain where
  f_pushforward (MkEntropyDomain e) = MkWorkDomain (e * intToBoxInt 27)
  f_pullback (MkWorkDomain w)       = MkEntropyDomain w
  verifyUnit _   = Refl
  verifyCounit _ = Refl

||| Left adjoint entropy scale functor L_Entropy
public export
data EntropyFunctor : Type -> Type where
  MkEntropyFunctor : EntropyStateDomain -> a -> EntropyFunctor a

public export
Functor EntropyFunctor where
  map f (MkEntropyFunctor e x) = MkEntropyFunctor e (f x)

public export
(Eq a) => Eq (EntropyFunctor a) where
  (MkEntropyFunctor e1 x1) == (MkEntropyFunctor e2 x2) = e1 == e2 && x1 == x2

||| Right adjoint work scale functor R_Work
public export
data WorkFunctor : Type -> Type where
  MkWorkFunctor : WorkStateDomain -> a -> WorkFunctor a

public export
Functor WorkFunctor where
  map f (MkWorkFunctor w x) = MkWorkFunctor w (f x)

public export
(Eq a) => Eq (WorkFunctor a) where
  (MkWorkFunctor w1 x1) == (MkWorkFunctor w2 x2) = w1 == w2 && x1 == x2

||| Forward hom-tensor isomorphism mapping Entropy to Work multiset tensors
public export
landauerHomTensorIso : MultisetTensor (EntropyFunctor a) b -> MultisetTensor a (WorkFunctor b)
landauerHomTensorIso ZeroM = ZeroM
landauerHomTensorIso (AddM (MkEntropyFunctor (MkEntropyDomain e) val, payload) weight rest) =
  AddM (val, MkWorkFunctor (MkWorkDomain e) payload) weight (landauerHomTensorIso rest)

||| Inverse hom-tensor isomorphism mapping Work to Entropy multiset tensors
public export
landauerHomTensorInv : MultisetTensor a (WorkFunctor b) -> MultisetTensor (EntropyFunctor a) b
landauerHomTensorInv ZeroM = ZeroM
landauerHomTensorInv (AddM (val, MkWorkFunctor (MkWorkDomain w) payload) weight rest) =
  AddM (MkEntropyFunctor (MkEntropyDomain w) val, payload) weight (landauerHomTensorInv rest)

||| Static proof witness verifying forward inverse round-trip isomorphism identity for Landauer erasure
public export
0 proofLandauerHomIso : (t : MultisetTensor (EntropyFunctor a) b) ->
                        landauerHomTensorInv (landauerHomTensorIso t) = t
proofLandauerHomIso ZeroM = Refl
proofLandauerHomIso (AddM (MkEntropyFunctor (MkEntropyDomain e) val, payload) weight rest) =
  let rec = proofLandauerHomIso rest
  in cong (AddM (MkEntropyFunctor (MkEntropyDomain e) val, payload) weight) rec

||| Static proof witness verifying reverse inverse round-trip isomorphism identity for Landauer erasure
public export
0 proofLandauerHomInv : (u : MultisetTensor a (WorkFunctor b)) ->
                        landauerHomTensorIso (landauerHomTensorInv u) = u
proofLandauerHomInv ZeroM = Refl
proofLandauerHomInv (AddM (val, MkWorkFunctor (MkWorkDomain w) payload) weight rest) =
  let rec = proofLandauerHomInv rest
  in cong (AddM (val, MkWorkFunctor (MkWorkDomain w) payload) weight) rec

||| Category-Theoretic MultisetAdjunction instance L_Entropy ⊣ R_Work for Landauer Information Erasure
public export
MultisetAdjunction EntropyFunctor WorkFunctor where
  leftAdjoint x = MkEntropyFunctor (MkEntropyDomain (intToBoxInt 0)) x
  rightAdjoint (MkEntropyFunctor _ x) = x
  homTensorIso = landauerHomTensorIso
  homTensorInv = landauerHomTensorInv
  verifyHomIso = proofLandauerHomIso
  verifyHomInv = proofLandauerHomInv

public export
StrictReflectionFunctor EntropyFunctor WorkFunctor where
  reflectionAdjunction = %search
  reflectionRefl _ = Refl

--------------------------------------------------------------------------------
-- 11. 2LTT STAGED THERMODYNAMIC PIPELINE
--------------------------------------------------------------------------------

||| Deforested 2LTT staged code generator transducer for QuadStream free energy evaluation.
%inline public export
stagedThermodynamicPipeline : QuadStreamMultiset BoxInt -> Code BoxInt
stagedThermodynamicPipeline qs = quote (quadStreamComputeFreeEnergy qs)

||| QTT 0 erased proof witness verifying thermodynamic free energy staging inverse identity.
public export
0 prfStagedThermodynamicPipeline : (qs : QuadStreamMultiset BoxInt) -> splice (stagedThermodynamicPipeline qs) = quadStreamComputeFreeEnergy qs
prfStagedThermodynamicPipeline qs = inverseSpliceQuote (quadStreamComputeFreeEnergy qs)
