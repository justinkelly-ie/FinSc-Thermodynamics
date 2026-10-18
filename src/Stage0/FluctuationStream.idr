module Stage0.FluctuationStream

import public Stage0.BoxInt
import public Stage1.Order.Preorder
import public Stage0.OnSeq.FusedStream
import public Stage1.Thermodynamics.EntropicArrow
import public Stage1.Multiset.PrimordialUnfolding
import Stage0.StructuralFuel
import Data.Fuel

%default total

--------------------------------------------------------------------------------
-- 1. THERMODYNAMIC WORK & HEAT FLUCTUATION STREAM ALGEBRA
--------------------------------------------------------------------------------

||| Discrete thermodynamic fluctuation step containing work done W and heat exchanged Q.
public export
record FluctuationStep where
  constructor MkFluctuation
  stepId   : Int
  workDone : BoxInt
  heatLoss : BoxInt

public export
Eq FluctuationStep where
  (MkFluctuation id1 w1 q1) == (MkFluctuation id2 w2 q2) =
    id1 == id2 && w1 == w2 && q1 == q2

||| Unfolds a list of work values into a deforested FluctuationStream.
%inline public export
unfoldWorkStream : List BoxInt -> FusedStream FluctuationStep
unfoldWorkStream workList = MkStream nextStep (1, workList)
  where
    nextStep : (Int, List BoxInt) -> Step (Int, List BoxInt) FluctuationStep
    nextStep (_, []) = Done
    nextStep (idx, w :: ws) = Yield (MkFluctuation idx w (intToBoxInt 0)) (idx + 1, ws)

||| Folds total work done directly across a deforested thermodynamic fluctuation stream.
public export
fusedTotalWorkStream : Fuel -> FusedStream FluctuationStep -> BoxInt
fusedTotalWorkStream f strm =
  foldStreamFuel f (\acc, step => addBox (workDone step) acc) (intToBoxInt 0) strm

||| Folds total work done across a deforested thermodynamic fluctuation stream using fueled fold.
public export
fusedTotalWork : Fuel -> List BoxInt -> BoxInt
fusedTotalWork f workList =
  fusedTotalWorkStream f (unfoldWorkStream workList)

||| Folds total work done across a deforested thermodynamic fluctuation stream using total structural Nat fuel.
public export
fusedTotalWorkNat : Nat -> List BoxInt -> BoxInt
fusedTotalWorkNat fuel workList =
  foldStreamNat fuel (\acc, step => addBox (workDone step) acc) (intToBoxInt 0) (unfoldWorkStream workList)

||| Folds total work done across a deforested thermodynamic fluctuation stream using model-indexed GohFuel.
public export
fusedTotalWorkFuelModel : GohFuel cap -> List BoxInt -> BoxInt
fusedTotalWorkFuelModel fuel workList =
  fusedTotalWorkNat (gohSteps fuel) workList

||| Evaluates discrete Jarzynski-style exponent sum directly over a fluctuation stream:
public export
fusedJarzynskiLinearBoundStream : Fuel -> BoxInt -> FusedStream FluctuationStep -> BoxInt
fusedJarzynskiLinearBoundStream f beta strm =
  foldStreamFuel f (\acc, step => addBox (subBox (intToBoxInt 1) (mulBox beta (workDone step))) acc) (intToBoxInt 0) strm

||| Evaluates discrete Jarzynski-style exponent sum: \sum (1 - \beta * W)
||| as a discrete linear approximation of <e^{-\beta W}> over work fluctuation streams.
public export
fusedJarzynskiLinearBound : Fuel -> BoxInt -> List BoxInt -> BoxInt
fusedJarzynskiLinearBound f beta workList =
  fusedJarzynskiLinearBoundStream f beta (unfoldWorkStream workList)

||| Evaluates discrete Jarzynski-style exponent sum using total structural Nat fuel.
public export
fusedJarzynskiLinearBoundNat : Nat -> BoxInt -> List BoxInt -> BoxInt
fusedJarzynskiLinearBoundNat fuel beta workList =
  foldStreamNat fuel (\acc, step => addBox (subBox (intToBoxInt 1) (mulBox beta (workDone step))) acc) (intToBoxInt 0) (unfoldWorkStream workList)

||| Evaluates discrete Jarzynski-style exponent sum using model-indexed GohFuel.
public export
fusedJarzynskiLinearBoundFuelModel : GohFuel cap -> BoxInt -> List BoxInt -> BoxInt
fusedJarzynskiLinearBoundFuelModel fuel beta workList =
  fusedJarzynskiLinearBoundNat (gohSteps fuel) beta workList

--------------------------------------------------------------------------------
-- 2. DEFORESTED ENTROPY DISSIPATION STREAM TRANSDUCERS & LANDAUER AUDIT
--------------------------------------------------------------------------------

||| Discrete entropy dissipation step recording erased bits and emitted heat in discrete units.
public export
record EntropyDissipationStep where
  constructor MkDissipationStep
  stepId      : Int
  erasedBits  : Nat
  emittedHeat : Nat

public export
Eq EntropyDissipationStep where
  (MkDissipationStep id1 b1 h1) == (MkDissipationStep id2 b2 h2) =
    id1 == id2 && b1 == b2 && h1 == h2

||| Unfolds a list of dissipation steps into a deforested stream.
public export
unfoldDissipationStream : List (Nat, Nat) -> FusedStream EntropyDissipationStep
unfoldDissipationStream steps = MkStream nextStep (1, steps)
  where
    nextStep : (Int, List (Nat, Nat)) -> Step (Int, List (Nat, Nat)) EntropyDissipationStep
    nextStep (_, []) = Done
    nextStep (idx, (b, h) :: rest) = Yield (MkDissipationStep idx b h) (idx + 1, rest)

||| Direct deforested stream transducer folding total emitted heat across entropy dissipation steps.
public export
fusedEntropyDissipationStreamDirect : Fuel -> FusedStream EntropyDissipationStep -> Nat
fusedEntropyDissipationStreamDirect f strm =
  foldStreamFuel f (\acc, step => emittedHeat step + acc) 0 strm

||| Direct deforested stream transducer folding total emitted heat across entropy dissipation steps over Nat fuel.
public export
fusedEntropyDissipationStreamNatDirect : Nat -> FusedStream EntropyDissipationStep -> Nat
fusedEntropyDissipationStreamNatDirect fuel strm =
  foldStreamNat fuel (\acc, step => emittedHeat step + acc) 0 strm

||| O(1) allocation deforested stream transducer folding total emitted heat across entropy dissipation steps.
public export
fusedEntropyDissipationStream : Fuel -> List (Nat, Nat) -> Nat
fusedEntropyDissipationStream f steps =
  fusedEntropyDissipationStreamDirect f (unfoldDissipationStream steps)

||| O(1) allocation deforested stream transducer folding total emitted heat across entropy dissipation steps over Nat fuel.
public export
fusedEntropyDissipationStreamNat : Nat -> List (Nat, Nat) -> Nat
fusedEntropyDissipationStreamNat fuel steps =
  fusedEntropyDissipationStreamNatDirect fuel (unfoldDissipationStream steps)

||| O(1) allocation deforested stream transducer folding total emitted heat over model-indexed GohFuel.
public export
fusedEntropyDissipationStreamFuelModel : GohFuel cap -> List (Nat, Nat) -> Nat
fusedEntropyDissipationStreamFuelModel fuel steps =
  fusedEntropyDissipationStreamNat (gohSteps fuel) steps

||| Direct deforested stream transducer folding total erased bits across entropy dissipation steps.
public export
fusedComputeTotalErasedBitsDirect : Fuel -> FusedStream EntropyDissipationStep -> Nat
fusedComputeTotalErasedBitsDirect f strm =
  foldStreamFuel f (\acc, step => erasedBits step + acc) 0 strm

||| O(1) allocation deforested stream transducer folding total erased bits across entropy dissipation steps.
public export
fusedComputeTotalErasedBits : Fuel -> List (Nat, Nat) -> Nat
fusedComputeTotalErasedBits f steps =
  fusedComputeTotalErasedBitsDirect f (unfoldDissipationStream steps)

||| Single-pass deforested stream transducer validating dynamic Landauer erasure bound
||| directly across an EntropyDissipationStep stream without multiple passes or list allocations.
public export
fusedValidateDynamicLandauerStreamDirect : Fuel -> (qBound : Nat) -> FusedStream EntropyDissipationStep -> Bool
fusedValidateDynamicLandauerStreamDirect f qBound strm =
  let (totalBits, totalHeat) =
        foldStreamFuel f (\acc, step => (fst acc + erasedBits step, snd acc + emittedHeat step)) (the (Nat, Nat) (0, 0)) strm
  in natLTE (totalBits * qBound) totalHeat

||| Single-pass deforested stream transducer validating dynamic Landauer erasure bound over Nat fuel.
public export
fusedValidateDynamicLandauerStreamNatDirect : Nat -> (qBound : Nat) -> FusedStream EntropyDissipationStep -> Bool
fusedValidateDynamicLandauerStreamNatDirect fuel qBound strm =
  let (totalBits, totalHeat) =
        foldStreamNat fuel (\acc, step => (fst acc + erasedBits step, snd acc + emittedHeat step)) (the (Nat, Nat) (0, 0)) strm
  in natLTE (totalBits * qBound) totalHeat

||| Deforested stream transducer validating dynamic Landauer erasure bound across entropy dissipation steps
||| scaled by active boundary quadrance qBound = Q_Blue = x^2 + y^2:
||| Total emitted heat must be >= totalBits * qBound.
public export
fusedValidateDynamicLandauerStream : Fuel -> (qBound : Nat) -> List (Nat, Nat) -> Bool
fusedValidateDynamicLandauerStream f qBound steps =
  fusedValidateDynamicLandauerStreamDirect f qBound (unfoldDissipationStream steps)

||| Deforested stream transducer validating dynamic Landauer erasure bound over Nat fuel.
public export
fusedValidateDynamicLandauerStreamNat : Nat -> (qBound : Nat) -> List (Nat, Nat) -> Bool
fusedValidateDynamicLandauerStreamNat fuel qBound steps =
  fusedValidateDynamicLandauerStreamNatDirect fuel qBound (unfoldDissipationStream steps)

||| Deforested stream transducer validating epoch-indexed Landauer erasure bound
||| where epoch index k determines dynamic boundary quadrance Q_Blue(x_k, y_k).
public export
fusedValidateEpochLandauerStream : Fuel -> (k : Nat) -> List (Nat, Nat) -> Bool
fusedValidateEpochLandauerStream f k steps =
  let (x, y) = epochPythagoreanCoordinate k
      qBlueNat = boxToNat (addBox (mulBox x x) (mulBox y y))
  in fusedValidateDynamicLandauerStream f qBlueNat steps

||| Deforested stream transducer validating epoch-indexed Landauer erasure bound over Nat fuel.
public export
fusedValidateEpochLandauerStreamNat : Nat -> (k : Nat) -> List (Nat, Nat) -> Bool
fusedValidateEpochLandauerStreamNat fuel k steps =
  let (x, y) = epochPythagoreanCoordinate k
      qBlueNat = boxToNat (addBox (mulBox x x) (mulBox y y))
  in fusedValidateDynamicLandauerStreamNat fuel qBlueNat steps

||| Deforested stream transducer validating Landauer erasure bound across entropy dissipation streams.
||| Deprecated: Prefer `fusedValidateDynamicLandauerStream` or `fusedValidateEpochLandauerStream`.
public export
fusedValidateLandauerStream : Fuel -> List (Nat, Nat) -> Bool
fusedValidateLandauerStream f steps =
  fusedValidateDynamicLandauerStream f 27 steps

||| Deforested stream transducer validating Landauer erasure bound over Nat fuel.
public export
fusedValidateLandauerStreamNat : Nat -> List (Nat, Nat) -> Bool
fusedValidateLandauerStreamNat fuel steps =
  fusedValidateDynamicLandauerStreamNat fuel 27 steps

--------------------------------------------------------------------------------
-- 3. VERIFICATION AUDIT WITNESS & LINEAR QTT ENTROPY TRANSDUCER
--------------------------------------------------------------------------------

||| Audit witness verifying zero-allocation total work and entropy dissipation stream folding.
public export
auditFluctuationStreamProof : Bool
auditFluctuationStreamProof =
  let works = [intToBoxInt 2, intToBoxInt 3, intToBoxInt 5]
      totW = fusedTotalWorkNat (length works) works
      jBound = fusedJarzynskiLinearBoundNat (length works) (intToBoxInt 1) works
      dissSteps = [(1, 27), (2, 60), (3, 90)]
      totHeat = fusedEntropyDissipationStreamNat (length dissSteps) dissSteps
      landauerValid = fusedValidateLandauerStreamNat (length dissSteps) dissSteps
      dynamicLandauerValid = fusedValidateEpochLandauerStreamNat (length dissSteps) 0 dissSteps
  in totW == intToBoxInt 10 && jBound == intToBoxInt (-7) && totHeat == 177 && landauerValid == True && dynamicLandauerValid == True

||| Strictly linear QTT entropy production stream transducer:
public export
record LinearEntropyTransducer where
  constructor MkLinearEntropyTransducer
  stepEntropyProduction : (1 strm : FusedStream FluctuationStep) -> FusedStream (BoxInt, Bool)

public export
linearEntropyTransducer : LinearEntropyTransducer
linearEntropyTransducer =
  MkLinearEntropyTransducer (\(MkStream next seed) =>
    MkStream (\s => case next s of
                      Done => Done
                      Skip s' => Skip s'
                      Yield step s' =>
                        let q = heatLoss step
                            nonNeg = q >= intToBoxInt 0
                        in Yield (q, nonNeg) s') seed)

||| Audits that open-system thermodynamic dissipation satisfies monotonic non-negative entropy production.
public export
auditStreamingEntropyProductionProof : Bool
auditStreamingEntropyProductionProof =
  let steps = [ MkFluctuation 1 (intToBoxInt 5) (intToBoxInt 2)
              , MkFluctuation 2 (intToBoxInt 8) (intToBoxInt 4) ]
      strm = linearEntropyTransducer.stepEntropyProduction (stream steps)
      (count, allNonNeg) =
        foldStreamNat (length steps)
          (\(cnt, ok), (_, nonNeg) => (cnt + 1, ok && nonNeg))
          (0, True)
          strm
  in count == 2 && allNonNeg

--------------------------------------------------------------------------------
-- 4. SINGLE-PASS HELMHOLTZ FREE ENERGY & PARTITION FUNCTION ACCUMULATOR
--------------------------------------------------------------------------------

||| Accumulates discrete Boltzmann state energy weights over a deforested stream:
||| Z_discrete = \sum w_i * (1 - \beta * E_i)
public export
fusedPartitionSumStream : Fuel -> BoxInt -> FusedStream (BoxInt, BoxInt) -> BoxInt
fusedPartitionSumStream f beta strm =
  foldStreamFuel f
    (\acc, (e, w) =>
      let term = mulBox w (subBox (intToBoxInt 1) (mulBox beta e))
      in addBox acc term)
    (intToBoxInt 0)
    strm

||| Single-pass discrete Helmholtz Free Energy accumulator F = U - TS:
||| Computes internal energy U and entropy dissipation S simultaneously over a fluctuation stream.
public export
fusedHelmholtzFreeEnergyStream : Fuel -> BoxInt -> FusedStream FluctuationStep -> BoxInt
fusedHelmholtzFreeEnergyStream f temp strm =
  let (u, s) =
        foldStreamFuel f
          (\(uAcc, sAcc), step => (addBox uAcc (workDone step), addBox sAcc (heatLoss step)))
          (intToBoxInt 0, intToBoxInt 0)
          strm
  in subBox u (mulBox temp s)

||| Single-pass discrete Helmholtz Free Energy accumulator F = U - TS directly from
||| streaming pairs of (energy, count) without intermediate list allocation.
public export
streamThermalFreeEnergy : Fuel -> BoxInt -> FusedStream (BoxInt, BoxInt) -> BoxInt
streamThermalFreeEnergy f temp strm =
  let (u, s) =
        foldStreamFuel f
          (\(uAcc, sAcc), (e, count) =>
            (addBox uAcc (mulBox e count), addBox sAcc count))
          (intToBoxInt 0, intToBoxInt 0)
          strm
  in subBox u (mulBox temp s)

||| Nat fuel-bounded single-pass discrete Helmholtz Free Energy accumulator F = U - TS.
public export
streamThermalFreeEnergyNat : (fuel : Nat) -> BoxInt -> FusedStream (BoxInt, BoxInt) -> BoxInt
streamThermalFreeEnergyNat f temp strm =
  let (u, s) =
        foldStreamNat f
          (\(uAcc, sAcc), (e, count) =>
            (addBox uAcc (mulBox e count), addBox sAcc count))
          (intToBoxInt 0, intToBoxInt 0)
          strm
  in subBox u (mulBox temp s)

||| Audit witness verifying direct streaming thermal free energy computation.
public export
auditDirectThermalFreeEnergyProof : Bool
auditDirectThermalFreeEnergyProof =
  let hadronPairs = [ (intToBoxInt 5, intToBoxInt 2)
                    , (intToBoxInt 20, intToBoxInt 3)
                    ]
      strm = stream hadronPairs
      temp = intToBoxInt 10
      f = streamThermalFreeEnergyNat 100 temp strm
  in f == intToBoxInt 20


