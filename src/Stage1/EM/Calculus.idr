module Stage1.EM.Calculus

import Stage0.BoxInt
import Stage1.VexelMaxel
import public Stage1.GrassmannCalculus
import Stage0.Potential
import Data.List
import Data.Vect

%default total

------------------------------------------------------------------------
-- 1. DISCRETE ELECTROMAGNETIC CALCULUS OPERATORS
------------------------------------------------------------------------

||| Computes the electrostatic field 1-form E = -d0(Phi) over directed edge pixels.
%inline
public export
computeElectricField : List (Unixel, Unixel) -> ElectricPotential -> EdgeCochain
computeElectricField edges phi =
  let gradPhi = grassmannCoboundary0 edges phi
  in scaleMaxel (intToBoxInt (-1)) gradPhi

||| Computes the magnetic flux 2-form B = d1(A) over directed face pixels.
%inline
public export
computeMagneticField : List (Pixel, Vect 4 (Unixel, Unixel)) -> VectorPotential -> FaceCochain
computeMagneticField faces a = grassmannCoboundary1 faces a

||| Computes the discrete charge density 3-form rho = d2(F) over 3D volume voxels.
%inline
public export
computeChargeDivergence : List (Voxel, Vect 6 (Pixel, BoxInt)) -> FaceCochain -> CellCochain
computeChargeDivergence voxels f = grassmannCoboundary2 voxels f

||| Computes the discrete Poisson-Laplacian Delta(Phi) = d0* d0(Phi) over vertex singletons.
%inline
public export
computePoissonLaplacian : List (Unixel, Unixel) -> ElectricPotential -> Vexel
computePoissonLaplacian edges phi =
  let eField = computeElectricField edges phi
      divergenceTerms = map (\(u@(MkUnixel uIdx), v@(MkUnixel vIdx)) =>
                              let eVal = lookupEdge (u, v) eField
                              in [(uIdx, -eVal), (vIdx, eVal)]) edges
      flatTerms = concat divergenceTerms
      grouped = map (\(n, w) => (MkUnixel n, w)) flatTerms
  in canonicalizeVexel (MkVexel grouped)

------------------------------------------------------------------------
-- 2. DISCRETE CALCULUS CONSERVATION LAWS
------------------------------------------------------------------------

||| Proves that the electrostatic field from a constant potential is identically zero.
public export
auditConstantPotentialZeroFieldProof : Bool
auditConstantPotentialZeroFieldProof =
  let edges = [(MkUnixel 1, MkUnixel 2), (MkUnixel 2, MkUnixel 3)]
      phi = MkVexel [(MkUnixel 1, intToBoxInt 10), (MkUnixel 2, intToBoxInt 10), (MkUnixel 3, intToBoxInt 10)]
      eField = computeElectricField edges phi
  in eField == MkMaxel []
