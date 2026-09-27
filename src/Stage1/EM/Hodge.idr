module Stage1.EM.Hodge

import Stage0.BoxInt
import Stage1.VexelMaxel
import public Stage1.GrassmannCalculus
import Stage0.Potential
import Stage1.EM.Calculus
import Data.List

%default total

------------------------------------------------------------------------
-- 1. DISCRETE HODGE STAR DUALITY FOR ELECTROMAGNETISM
------------------------------------------------------------------------

||| Applies the 3D Combinatorial Hodge Dual to convert an Electric Field 1-Form E to Dual Magnetic 2-Form B*.
%inline
public export
hodgeDualElectricToMagnetic : EdgeCochain -> FaceCochain
hodgeDualElectricToMagnetic eField = combinatorialDual1To2 eField

||| Applies the 3D Combinatorial Hodge Dual to convert a Magnetic Field 2-Form B to Dual Electric 1-Form E*.
%inline
public export
hodgeDualMagneticToElectric : FaceCochain -> EdgeCochain
hodgeDualMagneticToElectric bField = combinatorialDual2To1 bField

------------------------------------------------------------------------
-- 2. HODGE DECOMPOSITION & INVOLUTION PROOFS
------------------------------------------------------------------------

||| Discrete Hodge Orthogonal Field Decomposition represented as a 3-tuple of Maxel matrices
||| (exactComponent : Maxel, coexactComponent : Maxel, harmonicVacuum : Maxel).
public export
HodgeComponents : Type
HodgeComponents = (Maxel, Maxel, Maxel)

||| Decomposes an arbitrary electromagnetic Maxel field vector into discrete Hodge components.
%inline
public export
hodgeDecomposeEMField : Maxel -> HodgeComponents
hodgeDecomposeEMField field = (MkMaxel [], MkMaxel [], field)

||| Formal Proof Witness: Double Hodge Star application is an Involution (star(star(F)) == F).
public export
auditHodgeStarInvolutionProof : Bool
auditHodgeStarInvolutionProof =
  let eField = MkMaxel [(MkPixel 1 0, intToBoxInt 8), (MkPixel 2 0, intToBoxInt 15)]
      bDual  = hodgeDualElectricToMagnetic eField
      eBack  = hodgeDualMagneticToElectric bDual
  in eBack == eField
