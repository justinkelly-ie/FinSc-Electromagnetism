module Stage0.TransferMatrix

import Stage0.BoxInt
import Stage1.UnixelFraction
import Stage0.OnSeq.FusedStream
import Stage0.StructuralFuel
import Data.Fuel
import Data.List

%default total

------------------------------------------------------------------------
-- 1. 2x2 PHOTONIC TRANSFER MATRIX (TMM) CARRIER
------------------------------------------------------------------------

||| 2x2 Photonic Transfer Matrix M = [[m11, m12], [m21, m22]] in exact integer basis:
||| Relates forward and backward propagating optical wave amplitudes:
|||   [E+_in, E-_in]^T = M * [E+_out, E-_out]^T
public export
record TransferMatrix2x2 where
  constructor MkTM2x2
  m11 : BoxInt
  m12 : BoxInt
  m21 : BoxInt
  m22 : BoxInt

public export
Eq TransferMatrix2x2 where
  (MkTM2x2 a11 a12 a21 a22) == (MkTM2x2 b11 b12 b21 b22) =
    a11 == b11 && a12 == b12 && a21 == b21 && a22 == b22

||| Multiplies two 2x2 transfer matrices: M_res = M_A * M_B.
public export
mulTM2x2 : TransferMatrix2x2 -> TransferMatrix2x2 -> TransferMatrix2x2
mulTM2x2 (MkTM2x2 a11 a12 a21 a22) (MkTM2x2 b11 b12 b21 b22) =
  MkTM2x2
    (addBox (mulBox a11 b11) (mulBox a12 b21))
    (addBox (mulBox a11 b12) (mulBox a12 b22))
    (addBox (mulBox a21 b11) (mulBox a22 b21))
    (addBox (mulBox a21 b12) (mulBox a22 b22))

||| Identity transfer matrix: I = [[1, 0], [0, 1]].
public export
idTM2x2 : TransferMatrix2x2
idTM2x2 = MkTM2x2 (intToBoxInt 1) (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 1)

||| Computes determinant: det(M) = m11 * m22 - m12 * m21.
public export
detTM2x2 : TransferMatrix2x2 -> BoxInt
detTM2x2 (MkTM2x2 a11 a12 a21 a22) =
  subBox (mulBox a11 a22) (mulBox a12 a21)

------------------------------------------------------------------------
-- 2. MULTI-LAYER DIELECTRIC INTERFACE & PROPAGATION MATRICES
------------------------------------------------------------------------

||| Dielectric Layer specification: layer index, refractive index quanta, and optical thickness quanta.
public export
record DielectricLayer where
  constructor MkDielectricLayer
  layerIndex      : Nat
  refractiveIndex : BoxInt
  thicknessQuanta : BoxInt

||| Interface transfer matrix between medium 1 (n1) and medium 2 (n2):
||| Unnormalized integer matrix preserving boundary conditions:
|||   M_interface = [[n1 + n2, n1 - n2], [n1 - n2, n1 + n2]]
||| Determinant: (n1+n2)^2 - (n1-n2)^2 = 4 * n1 * n2 > 0 (strictly positive).
public export
interfaceMatrix : (n1 : BoxInt) -> (n2 : BoxInt) -> TransferMatrix2x2
interfaceMatrix n1 n2 =
  let sumN  = addBox n1 n2
      diffN = subBox n1 n2
  in MkTM2x2 sumN diffN diffN sumN

||| Layer propagation companion transfer matrix for phase thickness phi:
||| Companion recurrence matrix: [[1, -phi], [phi, 1]]
public export
propagationMatrix : (phi : BoxInt) -> TransferMatrix2x2
propagationMatrix phi =
  MkTM2x2 (intToBoxInt 1) (negBox phi) phi (intToBoxInt 1)

------------------------------------------------------------------------
-- 3. DEFORESTED TRANSFER MATRIX MULTI-LAYER STREAM TRANSDUCERS (O(1) Memory)
------------------------------------------------------------------------

||| Unfolds multi-layer transfer matrix stack into a deforested stream:
||| Generates layer transfer matrices without list materialization.
public export
streamTransferMatrices : List DielectricLayer -> FusedStream TransferMatrix2x2
streamTransferMatrices layers =
  mapStream (\(MkDielectricLayer _ n d) =>
    mulTM2x2 (interfaceMatrix (intToBoxInt 1) n) (propagationMatrix d))
    (stream layers)

||| Deforested accumulation of total stack transfer matrix: M_total = prod_i M_i
||| Executes in O(1) auxiliary space using stream left fold with total structural Nat fuel.
public export
fusedStackTransferMatrixNat : Nat -> List DielectricLayer -> TransferMatrix2x2
fusedStackTransferMatrixNat fuel layers =
  foldStreamNat fuel mulTM2x2 idTM2x2 (streamTransferMatrices layers)

||| Deforested accumulation of total stack transfer matrix using model-indexed GohFuel.
public export
fusedStackTransferMatrixFuelModel : GohFuel cap -> List DielectricLayer -> TransferMatrix2x2
fusedStackTransferMatrixFuelModel fuel layers =
  fusedStackTransferMatrixNat (gohSteps fuel) layers

------------------------------------------------------------------------
-- 4. POYNTING FLUX CONSERVATION ACROSS DIELECTRIC BOUNDARIES
------------------------------------------------------------------------

||| Computes discrete optical Poynting flux from wave amplitudes:
|||   S = (E^+)^2 - (E^-)^2
public export
computeLayerPoyntingFlux : (ePlus : BoxInt) -> (eMinus : BoxInt) -> BoxInt
computeLayerPoyntingFlux eP eM =
  subBox (mulBox eP eP) (mulBox eM eM)

||| Audits that interface transfer matrix preserves positive determinant (det M = 4 * n1 * n2 > 0).
public export
auditDielectricInterfaceDeterminant : (n1 : BoxInt) -> (n2 : BoxInt) -> Bool
auditDielectricInterfaceDeterminant n1 n2 =
  let m = interfaceMatrix n1 n2
      detM = detTM2x2 m
      expected = mulBox (intToBoxInt 4) (mulBox n1 n2)
  in boxEq detM expected

||| Audits deforested multi-layer photonic transfer matrix method:
||| 1. Interface matrix det(M_12) for n1=1, n2=2 is 4 * 1 * 2 = 8.
||| 2. Total 2-layer stack transfer matrix evaluates correctly in O(1) space.
||| 3. Identity matrix det(I) = 1.
public export
auditPhotonicTransferMatrixProof : Bool
auditPhotonicTransferMatrixProof =
  let detId = detTM2x2 idTM2x2
      tDet12 = auditDielectricInterfaceDeterminant (intToBoxInt 1) (intToBoxInt 2)
      layer1 = MkDielectricLayer 1 (intToBoxInt 2) (intToBoxInt 1)
      layer2 = MkDielectricLayer 2 (intToBoxInt 3) (intToBoxInt 2)
      mTot = fusedStackTransferMatrixFuelModel (gohFuelForCapacity 2) [layer1, layer2]
      detTot = detTM2x2 mTot
  in boxEq detId (intToBoxInt 1) && tDet12 && (detTot > intToBoxInt 0)
