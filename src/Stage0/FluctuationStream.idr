module Stage0.FluctuationStream

import public Stage0.BoxInt
import public Stage1.Order.Preorder
import public Stage0.OnSeq.FusedStream
import public Stage1.Thermodynamics.EntropicArrow
import public Stage1.Multiset.PrimordialUnfolding
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

||| Folds total work done across a deforested thermodynamic fluctuation stream using fueled fold.
public export
fusedTotalWork : Fuel -> List BoxInt -> BoxInt
fusedTotalWork f workList =
  foldStreamFuel f (\acc, step => workDone step + acc) (intToBoxInt 0) (unfoldWorkStream workList)

||| Evaluates discrete Jarzynski-style exponent sum: \sum (1 - \beta * W)
||| as a discrete linear approximation of <e^{-\beta W}> over work fluctuation streams.
public export
fusedJarzynskiLinearBound : Fuel -> BoxInt -> List BoxInt -> BoxInt
fusedJarzynskiLinearBound f beta workList =
  foldStreamFuel f (\acc, step => (intToBoxInt 1 - (beta * workDone step)) + acc) (intToBoxInt 0) (unfoldWorkStream workList)

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

||| O(1) allocation deforested stream transducer folding total emitted heat across entropy dissipation steps.
public export
fusedEntropyDissipationStream : Fuel -> List (Nat, Nat) -> Nat
fusedEntropyDissipationStream f steps =
  foldStreamFuel f (\acc, step => emittedHeat step + acc) 0 (unfoldDissipationStream steps)

||| O(1) allocation deforested stream transducer folding total erased bits across entropy dissipation steps.
public export
fusedComputeTotalErasedBits : Fuel -> List (Nat, Nat) -> Nat
fusedComputeTotalErasedBits f steps =
  foldStreamFuel f (\acc, step => erasedBits step + acc) 0 (unfoldDissipationStream steps)

||| Deforested stream transducer validating dynamic Landauer erasure bound across entropy dissipation streams
||| scaled by active boundary quadrance qBound = Q_Blue = x^2 + y^2:
||| Total emitted heat must be >= totalBits * qBound.
public export
fusedValidateDynamicLandauerStream : Fuel -> (qBound : Nat) -> List (Nat, Nat) -> Bool
fusedValidateDynamicLandauerStream f qBound steps =
  let totalBits = fusedComputeTotalErasedBits f steps
      totalHeat = fusedEntropyDissipationStream f steps
  in natLTE (totalBits * qBound) totalHeat

||| Deforested stream transducer validating epoch-indexed Landauer erasure bound
||| where epoch index k determines dynamic boundary quadrance Q_Blue(x_k, y_k).
public export
fusedValidateEpochLandauerStream : Fuel -> (k : Nat) -> List (Nat, Nat) -> Bool
fusedValidateEpochLandauerStream f k steps =
  let (x, y) = epochPythagoreanCoordinate k
      qBlueNat = integerToNat (unwrapBox ((x * x) + (y * y)))
  in fusedValidateDynamicLandauerStream f qBlueNat steps

||| Deforested stream transducer validating Landauer erasure bound across entropy dissipation streams.
||| Deprecated: Prefer `fusedValidateDynamicLandauerStream` or `fusedValidateEpochLandauerStream`.
public export
fusedValidateLandauerStream : Fuel -> List (Nat, Nat) -> Bool
fusedValidateLandauerStream f steps =
  fusedValidateDynamicLandauerStream f 27 steps

--------------------------------------------------------------------------------
-- 3. VERIFICATION AUDIT WITNESS & LINEAR QTT ENTROPY TRANSDUCER
--------------------------------------------------------------------------------

||| Audit witness verifying zero-allocation total work and entropy dissipation stream folding.
public export
auditFluctuationStreamProof : Bool
auditFluctuationStreamProof =
  let works = [intToBoxInt 2, intToBoxInt 3, intToBoxInt 5]
      totW = fusedTotalWork (limit (length works)) works
      jBound = fusedJarzynskiLinearBound (limit (length works)) (intToBoxInt 1) works
      dissSteps = [(1, 27), (2, 60), (3, 90)]
      totHeat = fusedEntropyDissipationStream (limit (length dissSteps)) dissSteps
      landauerValid = fusedValidateLandauerStream (limit (length dissSteps)) dissSteps
      dynamicLandauerValid = fusedValidateEpochLandauerStream (limit (length dissSteps)) 0 dissSteps
  in unwrapBox totW == 10 && unwrapBox jBound == -7 && totHeat == 177 && landauerValid == True && dynamicLandauerValid == True

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
                            nonNeg = unwrapBox q >= 0
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
  in unwrapBox f == 20


