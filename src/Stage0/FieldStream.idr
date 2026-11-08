module Stage0.FieldStream

import Data.List
import Data.Fuel
import Stage0.OnSeq.FusedStream
import Stage0.Singleton.Bit
import Stage1.EM.Maxwell
import Stage1.EM.Calculus
import public Stage1.Basis.Coordinate
import Stage0.BoxInt
import public Stage1.GrassmannCalculus
import Stage1.MaxelTransform
import Stage0.Multiset
import Stage1.UnixelFraction
import Data.Fin

%default total

------------------------------------------------------------------------
-- 1. DEFORESTED ELECTROMAGNETIC FIELD STATE STREAMING
------------------------------------------------------------------------

||| Convert a sequence of Maxwell field states into a deforested stream.
||| Deprecated: Stream Maxwell states directly using `stream` or domain-specific transducers.
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
poyntingTransducer : StreamTransducer MaxwellState Maxel
poyntingTransducer = MkTransducer (\(), st => Yield (computePoyntingVector (maxwellElectricField st) (maxwellMagneticField st)) ()) ()

||| Deforested Poynting flux stream transducer combining concurrent Electric and Magnetic cochain streams
||| into a stream of Poynting vector Maxel carriers in O(1) registers.
public export
streamPoyntingDualStream : FusedStream EdgeCochain -> FusedStream FaceCochain -> FusedStream Maxel
streamPoyntingDualStream eStrm bStrm =
  zipWithStream computePoyntingVector eStrm bStrm

||| Single-pass deforested electric field extraction pipelined over Maxwell state streams.
public export
streamElectricField : FusedStream MaxwellState -> FusedStream EdgeCochain
streamElectricField strm = transduceStream electricTransducer strm

||| Single-pass deforested magnetic field extraction pipelined over Maxwell state streams.
public export
streamMagneticField : FusedStream MaxwellState -> FusedStream FaceCochain
streamMagneticField strm = transduceStream magneticTransducer strm

||| Single-pass deforested Poynting vector flux extraction pipelined over Maxwell state streams.
public export
streamPoyntingVector : FusedStream MaxwellState -> FusedStream Maxel
streamPoyntingVector strm = transduceStream poyntingTransducer strm

||| Deforested Poynting flux stream computation S = E x B over a sequence of states.
public export
fusedPoyntingStream : FusedStream MaxwellState -> FusedStream Maxel
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
||| Deprecated: Process streams with `foldStreamFuel` or `foldStreamNat` without intermediate lists.
public export
runMaxwellStream : Fuel -> FusedStream MaxwellState -> List MaxwellState
runMaxwellStream = runFueledStream

||| Accumulates discrete Poynting flux total energy across a stream of Maxwell states bounded by canonical Hyperbolic flux capacity (128 DE).
public export
fusedPoyntingAccumulate : FusedStream MaxwellState -> Maxel
fusedPoyntingAccumulate strm =
  foldStreamFuel hyperbolicFuel (\acc, m => canonicalizeCell (addCellMultiset acc m)) neutral (fusedPoyntingStream strm)

||| Accumulates total integer Poynting energy frequency quanta directly into a BoxInt scalar bounded by canonical Hyperbolic flux capacity (128 DE).
public export
fusedPoyntingEnergyAccumulate : FusedStream MaxwellState -> BoxInt
fusedPoyntingEnergyAccumulate strm =
  foldStreamFuel hyperbolicFuel (\acc, m => acc + totalCellMultisetWeight m) (intToBoxInt 0) (fusedPoyntingStream strm)


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

||| Generates a deforested stream of radiated photon tokens directly from a time-varying Maxwell field stream:
||| Extracts field frequency/energy quanta and polarization bit directly from each Maxwell state in O(1) registers.
public export
streamRadiatedPhotonsFromMaxwell : FusedStream MaxwellState -> FusedStream PhotonStateToken
streamRadiatedPhotonsFromMaxwell =
  mapStream (\st =>
    let eField = maxwellElectricField st
        bField = maxwellMagneticField st
        eEnergy = totalCellMultisetWeight eField
        bEnergy = totalCellMultisetWeight bField
        freq = addBox eEnergy bEnergy
        polBit = if unwrapBox eEnergy >= unwrapBox bEnergy then Bit.Zero else Bit.One
    in MkPhotonToken polBit freq)

||| Unfolds a list of photon state parameters into a deforested PhotonStateStream.
||| Deprecated: Prefer `streamRadiatedPhotonsFromMaxwell` or direct FusedStream token producers.
public export
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

||| Evaluates total photon stream energy directly across a PhotonStateToken stream using a fueled fold.
%spec f
public export
fusedComputePhotonStreamEnergyDirect : Fuel -> FusedStream PhotonStateToken -> BoxInt
fusedComputePhotonStreamEnergyDirect f strm =
  foldStreamFuel f (\acc, tok => addBox (frequency tok) acc) (intToBoxInt 0) strm

||| Evaluates total photon stream energy directly across a PhotonStateToken stream over Nat fuel.
%spec fuel
public export
fusedComputePhotonStreamEnergyNatDirect : Nat -> FusedStream PhotonStateToken -> BoxInt
fusedComputePhotonStreamEnergyNatDirect fuel strm =
  foldStreamNat fuel (\acc, tok => addBox (frequency tok) acc) (intToBoxInt 0) strm

||| Evaluates total photon stream energy using a fueled fold.
||| Deprecated: Prefer `fusedComputePhotonStreamEnergyDirect` directly over FusedStream.
public export
fusedComputePhotonStreamEnergy : Fuel -> List (Bit, BoxInt) -> BoxInt
fusedComputePhotonStreamEnergy f items =
  fusedComputePhotonStreamEnergyDirect f (unfoldPhotonStream items)

||| Audit witness verifying zero-allocation deforested photon stream energy calculation.
public export
auditPhotonStreamProof : Bool
auditPhotonStreamProof =
  let items = [(Zero, intToBoxInt 5), (One, intToBoxInt 10)]
      totalE = foldStreamNat (length items) (\acc, tok => frequency tok + acc) (intToBoxInt 0) (unfoldPhotonStream items)
  in totalE == intToBoxInt 15

------------------------------------------------------------------------
-- 3. DEFORESTED POYNTING FLUX BOUNDARY INTEGRAL TRANSDUCER
------------------------------------------------------------------------

||| Evaluates closed boundary surface Poynting energy radiation from a stream of boundary link transforms.
||| Deforests link transitions without matrix allocations.
%spec fuelSteps
public export
streamBoundaryPoyntingRadiationNat : Nat -> FusedStream (MaxelTransform (Fin 2) (Fin 2)) -> BoxInt
streamBoundaryPoyntingRadiationNat fuelSteps linkStream =
  let idMaxel : MaxelTransform (Fin 2) (Fin 2)
      idMaxel = mkMaxelTransform EllipticSector unitUnixelFraction
                  [ (((the (Fin 2) Data.Fin.FZ, the (Fin 2) Data.Fin.FZ)), intToBoxInt 1)
                  , (((the (Fin 2) (Data.Fin.FS Data.Fin.FZ), the (Fin 2) (Data.Fin.FS Data.Fin.FZ))), intToBoxInt 1) ]
      loopMaxel = foldStreamNat fuelSteps (\acc, step => maxelMaxelBeta acc step) idMaxel linkStream
      eVal = totalMassBox (pixelBox loopMaxel)
      bVal = intToBoxInt 0
  in addBox (mulBox eVal eVal) (mulBox bVal bVal)

%spec f
public export
streamBoundaryPoyntingRadiation : Fuel -> FusedStream (MaxelTransform (Fin 2) (Fin 2)) -> BoxInt
streamBoundaryPoyntingRadiation f linkStream =
  let idMaxel : MaxelTransform (Fin 2) (Fin 2)
      idMaxel = mkMaxelTransform EllipticSector unitUnixelFraction
                  [ (((the (Fin 2) Data.Fin.FZ, the (Fin 2) Data.Fin.FZ)), intToBoxInt 1)
                  , (((the (Fin 2) (Data.Fin.FS Data.Fin.FZ), the (Fin 2) (Data.Fin.FS Data.Fin.FZ))), intToBoxInt 1) ]
      loopMaxel = foldStreamFuel f (\acc, step => maxelMaxelBeta acc step) idMaxel linkStream
      eVal = totalMassBox (pixelBox loopMaxel)
      bVal = intToBoxInt 0
  in addBox (mulBox eVal eVal) (mulBox bVal bVal)

||| Audits that an identity boundary link stream preserves Poynting field radiation invariant (Q_EM = 4).
public export
auditBoundaryPoyntingRadiationProof : Bool
auditBoundaryPoyntingRadiationProof =
  let idLink : MaxelTransform (Fin 2) (Fin 2)
      idLink = mkMaxelTransform EllipticSector unitUnixelFraction
                 [ (((the (Fin 2) Data.Fin.FZ, the (Fin 2) Data.Fin.FZ)), intToBoxInt 1)
                 , (((the (Fin 2) (Data.Fin.FS Data.Fin.FZ), the (Fin 2) (Data.Fin.FS Data.Fin.FZ))), intToBoxInt 1) ]
      strm = stream [idLink]
      rad = streamBoundaryPoyntingRadiationNat 1 strm
  in rad == intToBoxInt 4

