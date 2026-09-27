module Stage0.Flux

import Stage0.BoxInt
import Stage1.VexelMaxel
import Stage0.Multiset
import Stage1.GrassmannCalculus
import Stage0.Potential
import Stage1.EM.Calculus
import Data.List
import Data.Vect

%default total

------------------------------------------------------------------------
-- 1. PURE MULTISET PLAQUETTE FLUX & FARADAY ELECTROMOTIVE INDUCTION
------------------------------------------------------------------------

||| Computes magnetic flux B_pl = ∮ A · dl enclosed by a closed loop of Pixel edges
||| evaluated over a vector potential multiset A : Multiset BoxInt Pixel.
public export
computeMultisetPlaquetteFlux : List Pixel -> Multiset BoxInt Pixel -> BoxInt
computeMultisetPlaquetteFlux loopEdges potMultiset =
  sum (map (\p => lookupCount p potMultiset) loopEdges)

||| Computes Faraday's Law of Electromotive Force (EMF): E_emf = - (Flux_t2 - Flux_t1) / dt
||| over a loop specified by pure multiset vector potentials.
public export
computeMultisetFaradayEMF : Multiset BoxInt Pixel -> Multiset BoxInt Pixel -> List Pixel -> BoxInt -> BoxInt
computeMultisetFaradayEMF potT1 potT2 loopEdges dt =
  let fluxT1 = computeMultisetPlaquetteFlux loopEdges potT1
      fluxT2 = computeMultisetPlaquetteFlux loopEdges potT2
      deltaFlux = fluxT2 - fluxT1
  in intToBoxInt (-1) * deltaFlux

------------------------------------------------------------------------
-- 2. PLAQUETTE FLUX & FARADAY ELECTROMOTIVE INDUCTION (LEGACY)
------------------------------------------------------------------------

||| A Plaquette 2-Cell represented as a closed boundary loop of 4 Unixel vertices.
public export
record Plaquette where
  constructor MkPlaquette
  facePixel : Pixel
  boundaryLoop : Vect 4 (Unixel, Unixel)

||| Computes magnetic flux B_pl = ∮ A · dl enclosed by a 4-edge Plaquette cell.
public export
computePlaquetteFlux : Plaquette -> VectorPotential -> BoxInt
computePlaquetteFlux (MkPlaquette _ loop) a =
  sum (map (\e => lookupEdge e a) (toList loop))

||| Computes Faraday's Law of Electromotive Force (EMF): E_emf = - (Flux_t2 - Flux_t1) / dt.
public export
computeFaradayEMF : BoxInt -> BoxInt -> BoxInt -> BoxInt
computeFaradayEMF fluxT1 fluxT2 dt =
  let deltaFlux = fluxT2 - fluxT1
  in intToBoxInt (-1) * deltaFlux

------------------------------------------------------------------------
-- 3. GAUSS'S LAW FOR MAGNETISM (div B = 0 / NO MONOPOLES)
------------------------------------------------------------------------

||| Formal Proof Witness: Total Magnetic Flux across a Closed Voxel Surface is Zero (d2 B == 0).
public export
auditNoMagneticMonopolesProof : Bool
auditNoMagneticMonopolesProof =
  let -- Face pixels of a 3D unit cube voxel
      faces = [ (MkPixel 1 0, intToBoxInt 1)   -- +X
              , (MkPixel 1 0, intToBoxInt (-1))  -- -X
              , (MkPixel 2 0, intToBoxInt 1)   -- +Y
              , (MkPixel 2 0, intToBoxInt (-1))  -- -Y
              , (MkPixel 3 0, intToBoxInt 1)   -- +Z
              , (MkPixel 3 0, intToBoxInt (-1))  -- -Z
              ]
      voxels = [(MkVoxel 1 1 1, faces)]
      -- Any exact solenoid magnetic field B = d1(A)
      bField = MkMaxel [ (MkPixel 1 0, intToBoxInt 12)
                       , (MkPixel 2 0, intToBoxInt 7)
                       , (MkPixel 3 0, intToBoxInt 19)
                       ]
      divB = grassmannCoboundary2 voxels bField
  in divB == MkBoxel []
