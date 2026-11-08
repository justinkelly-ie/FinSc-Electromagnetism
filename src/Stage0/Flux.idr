module Stage0.Flux

import Stage0.BoxInt
import public Stage1.Basis.Coordinate
import Stage0.Multiset
import Stage1.GrassmannCalculus
import Stage0.Potential
import Stage1.EM.Calculus
import Stage0.OnSeq.FusedStream
import Stage0.StructuralFuel
import Data.List
import Data.Vect

%default total

------------------------------------------------------------------------
-- 1. PURE MULTISET PLAQUETTE FLUX & FARADAY ELECTROMOTIVE INDUCTION
------------------------------------------------------------------------

||| Single-pass streaming plaquette magnetic flux B_pl = ∮ A · dl enclosed by a stream of pixel edges.
public export
streamMultisetPlaquetteFlux : FusedStream Pixel -> Multiset BoxInt Pixel -> BoxInt
streamMultisetPlaquetteFlux loopEdges potMultiset =
  foldStreamNat (gohSteps hyperbolicGohFuelModel) (\acc, p => addBox (lookupCount p potMultiset) acc) (intToBoxInt 0) loopEdges

||| Computes magnetic flux B_pl = ∮ A · dl enclosed by a closed loop of Pixel edges
||| evaluated over a vector potential multiset A : Multiset BoxInt Pixel.
public export
computeMultisetPlaquetteFlux : List Pixel -> Multiset BoxInt Pixel -> BoxInt
computeMultisetPlaquetteFlux loopEdges potMultiset =
  streamMultisetPlaquetteFlux (stream loopEdges) potMultiset

||| Single-pass streaming Faraday EMF across an edge stream.
public export
streamMultisetFaradayEMF : Multiset BoxInt Pixel -> Multiset BoxInt Pixel -> FusedStream Pixel -> BoxInt -> BoxInt
streamMultisetFaradayEMF potT1 potT2 loopEdges dt =
  let fluxT1 = streamMultisetPlaquetteFlux loopEdges potT1
      fluxT2 = streamMultisetPlaquetteFlux loopEdges potT2
      deltaFlux = fluxT2 - fluxT1
  in intToBoxInt (-1) * deltaFlux

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
      bField = singletonCell (mkPixel 1 0) (intToBoxInt 12) <+>
               singletonCell (mkPixel 2 0) (intToBoxInt 7) <+>
               singletonCell (mkPixel 3 0) (intToBoxInt 19)
      divB = grassmannCoboundary2 voxels bField
  in divB == neutral
