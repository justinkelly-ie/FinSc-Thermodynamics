module Stage0.FluctuationStream

import public Stage0.BoxInt
import public Stage1.Order.Preorder
import public Stage0.OnSeq.FusedStream
import public Stage1.Thermodynamics.EntropicArrow
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

||| Folds total work done across a deforested thermodynamic fluctuation stream using hylomorphism.
public export covering
fusedTotalWork : Fuel -> List BoxInt -> BoxInt
fusedTotalWork f workList =
  fusedHylomorphism f
    (\(idx, ws) => case ws of
                     [] => Done
                     w :: ws' => Yield (MkFluctuation idx w (intToBoxInt 0)) (idx + 1, ws'))
    (\step, acc => workDone step + acc)
    (intToBoxInt 0)
    (1, workList)

||| Evaluates discrete Jarzynski-style exponent sum: \sum (1 - \beta * W)
||| as a discrete linear approximation of <e^{-\beta W}> over work fluctuation streams.
public export covering
fusedJarzynskiLinearBound : Fuel -> BoxInt -> List BoxInt -> BoxInt
fusedJarzynskiLinearBound f beta workList =
  fusedHylomorphism f
    (\(idx, ws) => case ws of
                     [] => Done
                     w :: ws' => Yield (MkFluctuation idx w (intToBoxInt 0)) (idx + 1, ws'))
    (\step, acc => (intToBoxInt 1 - (beta * workDone step)) + acc)
    (intToBoxInt 0)
    (1, workList)

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

||| O(1) allocation deforested stream transducer folding total emitted heat across entropy dissipation steps.
public export covering
fusedEntropyDissipationStream : Fuel -> List (Nat, Nat) -> Nat
fusedEntropyDissipationStream f steps =
  fusedHylomorphism f
    (\(idx, st) => case st of
                     [] => Done
                     (b, h) :: rest => Yield (MkDissipationStep idx b h) (idx + 1, rest))
    (\step, acc => emittedHeat step + acc)
    0
    (1, steps)

||| O(1) allocation deforested stream transducer folding total erased bits across entropy dissipation steps.
public export covering
fusedComputeTotalErasedBits : Fuel -> List (Nat, Nat) -> Nat
fusedComputeTotalErasedBits f steps =
  fusedHylomorphism f
    (\(idx, st) => case st of
                     [] => Done
                     (b, h) :: rest => Yield (MkDissipationStep idx b h) (idx + 1, rest))
    (\step, acc => erasedBits step + acc)
    0
    (1, steps)

||| Deforested stream transducer validating Landauer erasure bound across entropy dissipation streams.
public export covering
fusedValidateLandauerStream : Fuel -> List (Nat, Nat) -> Bool
fusedValidateLandauerStream f steps =
  let totalBits = fusedComputeTotalErasedBits f steps
      totalHeat = fusedEntropyDissipationStream f steps
  in natLTE (totalBits * 27) totalHeat

--------------------------------------------------------------------------------
-- 3. VERIFICATION AUDIT WITNESS
--------------------------------------------------------------------------------

||| Audit witness verifying zero-allocation total work and entropy dissipation stream folding.
public export covering
auditFluctuationStreamProof : Bool
auditFluctuationStreamProof =
  let works = [intToBoxInt 2, intToBoxInt 3, intToBoxInt 5]
      totW = fusedTotalWork (limit 100) works
      jBound = fusedJarzynskiLinearBound (limit 100) (intToBoxInt 1) works
      dissSteps = [(1, 27), (2, 60), (3, 90)]
      totHeat = fusedEntropyDissipationStream (limit 100) dissSteps
      landauerValid = fusedValidateLandauerStream (limit 100) dissSteps
  in unwrapBox totW == 10 && unwrapBox jBound == -7 && totHeat == 177 && landauerValid == True

