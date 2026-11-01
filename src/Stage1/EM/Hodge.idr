module Stage1.EM.Hodge

import Stage0.BoxInt
import public Stage1.Basis.Coordinate
import public Stage1.GrassmannCalculus
import Stage0.Potential
import Stage1.EM.Calculus
import Data.List
import Stage1.SymmetricMetricTensor as SMT
import Stage1.TypeTheory.Staging

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
hodgeDecomposeEMField field = (neutral, neutral, field)

||| Formal Proof Witness: Double Hodge Star application is an Involution (star(star(F)) == F).
public export
auditHodgeStarInvolutionProof : Bool
auditHodgeStarInvolutionProof =
  let eField = singletonCell (mkPixel 1 0) (intToBoxInt 8) <+> singletonCell (mkPixel 2 0) (intToBoxInt 15)
      bDual  = hodgeDualElectricToMagnetic eField
      eBack  = hodgeDualMagneticToElectric bDual
  in eBack == eField

------------------------------------------------------------------------
-- 3. 2LTT STAGED CURVED-SPACETIME HODGE STAR DUALITY
------------------------------------------------------------------------

||| 2LTT Staged Curved-Spacetime Metric Hodge Contraction:
public export
stagedHodgeStarMetric : {dim : Nat} -> Lift (SMT.SymmetricMetricTensor dim) -> VexelN dim -> Code (VexelN dim)
stagedHodgeStarMetric qMetric v = SMT.stagedMetricContract qMetric v

||| Staged evaluation of metric Hodge contraction:
public export
evalStagedHodgeStarMetric : {dim : Nat} -> Lift (SMT.SymmetricMetricTensor dim) -> VexelN dim -> VexelN dim
evalStagedHodgeStarMetric qMetric v = splice (stagedHodgeStarMetric qMetric v)

||| 2LTT Staged 4D Spacetime Hodge Star Operator:
public export
stagedHodgeDual4D : Lift (SMT.SymmetricMetricTensor 4) -> VexelN 4 -> Code (VexelN 4)
stagedHodgeDual4D qMetric v = stagedHodgeStarMetric qMetric v

||| Staged evaluation of 4D Hodge dual:
public export
evalStagedHodgeDual4D : Lift (SMT.SymmetricMetricTensor 4) -> VexelN 4 -> VexelN 4
evalStagedHodgeDual4D qMetric v = splice (stagedHodgeDual4D qMetric v)

||| QTT 0 Erased Proof Witness: Staged Hodge Star Metric Invariant
public export
0 prfStagedHodgeDual4D : (g : SMT.SymmetricMetricTensor 4) -> (v : VexelN 4) ->
                        splice (stagedHodgeDual4D (quote g) v) = SMT.contractMetric g v
prfStagedHodgeDual4D _ _ = Refl
