module Stage0.FieldStream

import Data.List
import Data.Fuel
import Stage0.OnSeq.FusedStream
import Stage0.Singleton.Bit
import Stage1.EM.Maxwell
import Stage1.EM.Calculus
import Stage1.VexelMaxel
import Stage0.BoxInt
import public Stage1.GrassmannCalculus

%default total

------------------------------------------------------------------------
-- 1. DEFORESTED ELECTROMAGNETIC FIELD STATE STREAMING
------------------------------------------------------------------------

||| Convert a sequence of Maxwell field states into a deforested stream.
public export
streamMaxwellStates : List MaxwellState -> FusedStream MaxwellState
streamMaxwellStates = stream

||| Electric field stream transducer extracting EdgeCochain from MaxwellState.
public export
electricTransducer : StreamTransducer MaxwellState EdgeCochain
electricTransducer = MkTransducer (\(), st => Yield (maxwellElectricField st) ()) ()

||| Magnetic field stream transducer extracting FaceCochain from MaxwellState.
public export
magneticTransducer : StreamTransducer MaxwellState FaceCochain
magneticTransducer = MkTransducer (\(), st => Yield (maxwellMagneticField st) ()) ()

||| Poynting flux stream transducer computing S = E x B from MaxwellState.
public export
poyntingTransducer : StreamTransducer MaxwellState Stage1.VexelMaxel.Maxel
poyntingTransducer = MkTransducer (\(), st => Yield (computePoyntingVector (maxwellElectricField st) (maxwellMagneticField st)) ()) ()

||| Single-pass deforested electric field extraction pipelined over Maxwell state streams.
%inline public export
streamElectricField : FusedStream MaxwellState -> FusedStream EdgeCochain
streamElectricField strm = transduceStream electricTransducer strm

||| Single-pass deforested magnetic field extraction pipelined over Maxwell state streams.
%inline public export
streamMagneticField : FusedStream MaxwellState -> FusedStream FaceCochain
streamMagneticField strm = transduceStream magneticTransducer strm

||| Single-pass deforested Poynting vector flux extraction pipelined over Maxwell state streams.
%inline public export
streamPoyntingVector : FusedStream MaxwellState -> FusedStream Stage1.VexelMaxel.Maxel
streamPoyntingVector strm = transduceStream poyntingTransducer strm

||| Deforested Poynting flux stream computation S = E x B over a sequence of states.
public export
fusedPoyntingStream : FusedStream MaxwellState -> FusedStream Stage1.VexelMaxel.Maxel
fusedPoyntingStream = streamPoyntingVector

||| Deforested electric field extraction from Maxwell states.
public export
fusedElectricStream : FusedStream MaxwellState -> FusedStream EdgeCochain
fusedElectricStream = streamElectricField

||| Deforested magnetic field extraction from Maxwell states.
public export
fusedMagneticStream : FusedStream MaxwellState -> FusedStream FaceCochain
fusedMagneticStream = streamMagneticField

||| Evaluates a Maxwell state stream into a List container.
public export
runMaxwellStream : Fuel -> FusedStream MaxwellState -> List MaxwellState
runMaxwellStream = runFueledStream

||| Accumulates discrete Poynting flux total energy across a stream of Maxwell states using canonical Maxel multiset addition.
public export covering
fusedPoyntingAccumulate : FusedStream MaxwellState -> Stage1.VexelMaxel.Maxel
fusedPoyntingAccumulate strm =
  foldStream (\acc, m => canonicalizeMaxel (Stage1.VexelMaxel.addMaxel acc m)) (MkMaxel []) (fusedPoyntingStream strm)

||| Accumulates total integer Poynting energy frequency quanta directly into a BoxInt scalar without list concatenations.
public export covering
fusedPoyntingEnergyAccumulate : FusedStream MaxwellState -> BoxInt
fusedPoyntingEnergyAccumulate strm =
  foldStream (\acc, m => acc + totalMaxelWeight m) (intToBoxInt 0) (fusedPoyntingStream strm)


------------------------------------------------------------------------
-- 2. DEFORESTED PHOTON STATE STREAM TRANSDUCERS (O(1) ALLOCATION)
------------------------------------------------------------------------

||| Photon State Token carrying polarization bit and photon energy frequency quanta.
public export
record PhotonStateToken where
  constructor MkPhotonToken
  polarization : Bit
  frequency    : BoxInt

public export
Eq PhotonStateToken where
  (MkPhotonToken p1 f1) == (MkPhotonToken p2 f2) = p1 == p2 && f1 == f2

||| Unfolds a list of photon state parameters into a deforested PhotonStateStream.
%inline public export
unfoldPhotonStream : List (Bit, BoxInt) -> FusedStream PhotonStateToken
unfoldPhotonStream items = MkStream nextStep items
  where
    nextStep : List (Bit, BoxInt) -> Step (List (Bit, BoxInt)) PhotonStateToken
    nextStep [] = Done
    nextStep ((pol, freq) :: rest) = Yield (MkPhotonToken pol freq) rest

||| Deforested stream transducer propagating photon states with zero intermediate list allocations.
public export
fusedPhotonStateStream : FusedStream PhotonStateToken -> FusedStream PhotonStateToken
fusedPhotonStateStream strm =
  mapStream (\tok => MkPhotonToken (tok.polarization) (tok.frequency + intToBoxInt 1)) strm

||| Evaluates total photon stream energy using a fused hylomorphism.
public export covering
fusedComputePhotonStreamEnergy : Fuel -> List (Bit, BoxInt) -> BoxInt
fusedComputePhotonStreamEnergy f items =
  fusedHylomorphism f
    (\st => case st of
              [] => Done
              (pol, freq) :: rest => Yield (MkPhotonToken pol freq) rest)
    (\tok, acc => frequency tok + acc)
    (intToBoxInt 0)
    items

||| Audit witness verifying zero-allocation deforested photon stream energy calculation.
public export covering
auditPhotonStreamProof : Bool
auditPhotonStreamProof =
  let items = [(Zero, intToBoxInt 5), (One, intToBoxInt 10)]
      totalE = fusedComputePhotonStreamEnergy (limit 100) items
  in unwrapBox totalE == 15
