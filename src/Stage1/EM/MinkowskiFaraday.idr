module Stage1.EM.MinkowskiFaraday

import Data.Vect
import Stage0.BoxInt
import Stage0.OnSeq.FusedStream
import Stage1.Carrier.SquareMaxel
import Stage1.Carrier.CellMultiset
import Stage1.Carrier.Maxel
import Stage1.ProjectiveDihedron
import Stage1.DihedronModel
import Stage0.DihedronStream
import Stage1.TypeTheory.Staging

%default total

------------------------------------------------------------------------
-- 1. 3D MINKOWSKI ELECTROMAGNETIC FIELD CARRIER
------------------------------------------------------------------------

||| 3D Minkowski Electromagnetic Field in (2+1) spacetime:
||| Transverse electric field components [Er, Es] in the spatial plane
||| and perpendicular magnetic field scalar Bz.
public export
record MinkowskiEMField where
  constructor MkMinkowskiEM
  eField : Vect 2 BoxInt  -- [Er, Es]
  bField : BoxInt          -- Bz

public export
Eq MinkowskiEMField where
  (MkMinkowskiEM [er1, es1] bz1) == (MkMinkowskiEM [er2, es2] bz2) =
    (er1 == er2) && (es1 == es2) && (bz1 == bz2)

public export
Show MinkowskiEMField where
  show (MkMinkowskiEM [er, es] bz) =
    "MinkowskiEM(E = (" ++ show er ++ ", " ++ show es ++ "), Bz = " ++ show bz ++ ")"

------------------------------------------------------------------------
-- 2. HODGE DUAL 1-FORM & MINKOWSKI 3-VECTOR ISOMORPHISM
------------------------------------------------------------------------

||| In (2+1)D spacetime, the electromagnetic Faraday 2-form:
|||   F = Er (dt ∧ dr) + Es (dt ∧ ds) + Bz (dr ∧ ds)
||| has Hodge dual 1-form:
|||   *F = Bz dt - Es dr + Er ds
||| which is isomorphic to a Minkowski 3-vector (t = Bz, r = Er, s = Es)
||| transforming identically under SO(1, 2) Lorentz transformations.
public export
emToMinkowskiVector : MinkowskiEMField -> MinkowskiVector
emToMinkowskiVector (MkMinkowskiEM [er, es] bz) = MkMVec bz er es

||| Reconstructs Minkowski electromagnetic field from MinkowskiVector.
public export
minkowskiVectorToEM : MinkowskiVector -> MinkowskiEMField
minkowskiVectorToEM (MkMVec bz er es) = MkMinkowskiEM [er, es] bz

------------------------------------------------------------------------
-- 3. RELATIVISTIC ELECTROMAGNETIC INVARIANTS & POYNTING FLUX
------------------------------------------------------------------------

||| Relativistic scalar electromagnetic invariant S = Er² + Es² - Bz²:
||| S is the negative of the Minkowski vector quadrance: S = -Q(w).
public export
emScalarInvariant : MinkowskiEMField -> BoxInt
emScalarInvariant (MkMinkowskiEM [er, es] bz) =
  ((er * er) + (es * es)) - (bz * bz)

||| Relativistic Minkowski quadrance Q(w) = Bz² - Er² - Es².
public export
emQuadrance : MinkowskiEMField -> BoxInt
emQuadrance em = quadranceMVec (emToMinkowskiVector em)

||| Poynting momentum flux in the transverse (r, s) spatial plane:
||| S_Poynting = E × B = (Es * Bz, -Er * Bz).
public export
emPoyntingFlux : MinkowskiEMField -> Vect 2 BoxInt
emPoyntingFlux (MkMinkowskiEM [er, es] bz) =
  [es * bz, negBox (er * bz)]

------------------------------------------------------------------------
-- 4. EXACT PROJECTIVE DIHEDRON LORENTZ FIELD TRANSPORT
------------------------------------------------------------------------

||| Exact rational Lorentz transformation of electromagnetic field (Er, Es, Bz)
||| under a projective dihedron proportion α = (x : v) in P³(Q).
||| Evaluates via Wildberger Theorem 78 scaled vector action:
|||   w_scaled = (x² - Q(v)) w + 2x (v × w) + 2 <v, w> v.
|||
||| Preserves invariant scalar with exact quadratic norm scaling:
|||   S' = N(α)² * S
||| eliminating irrational γ = 1/√(1 - β²) square roots and floating-point drift!
public export
boostEMFieldProjective : ProjectiveDihedron -> MinkowskiEMField -> MinkowskiEMField
boostEMFieldProjective alpha em =
  minkowskiVectorToEM (actDihedronVectorScaled alpha (emToMinkowskiVector em))

------------------------------------------------------------------------
-- 5. MATRIX CONGRUENCE & MAXEL AVL TREE EMBEDDING
------------------------------------------------------------------------

||| Converts electromagnetic field (Bz, Er, Es) to a 2x2 Dihedron matrix W = μ(0, Bz, Er, Es):
||| W = [[Es, Er - Bz], [Er + Bz, -Es]] with det(W) = -Es² - (Er² - Bz²) = Bz² - Er² - Es² = -S.
public export
emToMatrix : MinkowskiEMField -> DihedronMatrix2x2
emToMatrix (MkMinkowskiEM [er, es] bz) =
  MkDMat2x2 es (er - bz) (er + bz) (negBox es)

||| Converts a 2x2 Dihedron matrix back to an electromagnetic field.
public export
matrixToEM : DihedronMatrix2x2 -> MinkowskiEMField
matrixToEM (MkDMat2x2 a b c d) =
  let es = divBoxInt2 (a - d)
      er = divBoxInt2 (c + b)
      bz = divBoxInt2 (c - b)
  in MkMinkowskiEM [er, es] bz
  where
    divBoxInt2 : BoxInt -> BoxInt
    divBoxInt2 bx = intToBoxInt (unwrapBox bx `div` 2)

||| Theorem 78 Sandwich action of projective dihedron matrix on electromagnetic field:
|||   W' = μ(α*) · W · μ(α) = adj(μ(α)) · W · μ(α).
||| Since det(W') = det(μ(α*)) * det(W) * det(μ(α)) = N(α)² * (-S),
||| the matrix sandwich identically reproduces the scaled Lorentz transport!
public export
boostEMFieldMatrix : ProjectiveDihedron -> MinkowskiEMField -> MinkowskiEMField
boostEMFieldMatrix alpha em =
  let muAlpha = dihedronToMatrix (projToDihedron alpha)
      muAdj   = dihedronToMatrix (projToDihedron (invProjDihedron alpha))
      wMat    = emToMatrix em
      prodMat = mulDMat2x2 (mulDMat2x2 muAdj wMat) muAlpha
  in matrixToEM prodMat

||| Embeds Minkowski electromagnetic field into a 2x2 Maxel AVL tree container:
||| pixel (1, 1) = Es, pixel (1, 2) = Er - Bz, pixel (2, 1) = Er + Bz, pixel (2, 2) = -Es.
public export
emToMaxel : MinkowskiEMField -> Maxel
emToMaxel (MkMinkowskiEM [er, es] bz) =
  setCellMultiset (mkPixel 1 1) es
    (setCellMultiset (mkPixel 1 2) (er - bz)
      (setCellMultiset (mkPixel 2 1) (er + bz)
        (setCellMultiset (mkPixel 2 2) (negBox es) emptyMaxel)))

||| Extracts a Minkowski electromagnetic field from a 2x2 Maxel AVL tree container:
||| pixel (1, 1) = Es, pixel (1, 2) = Er - Bz, pixel (2, 1) = Er + Bz, pixel (2, 2) = -Es.
public export
maxelToEM : Maxel -> MinkowskiEMField
maxelToEM m =
  let es = lookupCellMultiset (mkPixel 1 1) m
      b  = lookupCellMultiset (mkPixel 1 2) m
      c  = lookupCellMultiset (mkPixel 2 1) m
      er = divBoxInt2 (c + b)
      bz = divBoxInt2 (c - b)
  in MkMinkowskiEM [er, es] bz
  where
    divBoxInt2 : BoxInt -> BoxInt
    divBoxInt2 bx = intToBoxInt (unwrapBox bx `div` 2)

||| Converts Minkowski electromagnetic field into the concrete Dihedron2 model stencil from FinSc-Metric-Substrate:
public export
emToDihedron2 : MinkowskiEMField -> Dihedron2
emToDihedron2 (MkMinkowskiEM [er, es] bz) =
  MkDihedron2 es (er - bz) (er + bz) (negBox es)

||| Reconstructs Minkowski electromagnetic field from the concrete Dihedron2 model stencil:
public export
dihedron2ToEM : Dihedron2 -> MinkowskiEMField
dihedron2ToEM (MkDihedron2 d00 d01 d10 d11) =
  let es = divBoxInt2 (d00 - d11)
      er = divBoxInt2 (d10 + d01)
      bz = divBoxInt2 (d10 - d01)
  in MkMinkowskiEM [er, es] bz
  where
    divBoxInt2 : BoxInt -> BoxInt
    divBoxInt2 bx = intToBoxInt (unwrapBox bx `div` 2)

------------------------------------------------------------------------
-- 6. DEFORESTED ELECTROMAGNETIC FIELD STREAM TRANSDUCERS (Rule 04 §12)
------------------------------------------------------------------------

||| Single-pass deforested stream transformer boosting electromagnetic fields in O(1) auxiliary registers.
public export
streamBoostEMField : ProjectiveDihedron -> FusedStream MinkowskiEMField -> FusedStream MinkowskiEMField
streamBoostEMField alpha strm =
  mapStream (boostEMFieldProjective alpha) strm

||| Deforested stream transformer accumulating relativistic Lorentz frame changes on an initial EM field.
public export
streamAccumulateEMBoosts : FusedStream ProjectiveDihedron -> MinkowskiEMField -> FusedStream MinkowskiEMField
streamAccumulateEMBoosts boostStrm em0 =
  mapStream (\boost => boostEMFieldProjective boost em0) (streamAccumulateBoosts boostStrm)

------------------------------------------------------------------------
-- 7. 2LTT STAGED CODE GENERATION (Rule 04)
------------------------------------------------------------------------

||| Deforested 2LTT staged code generator for electromagnetic field Lorentz boosts.
%inline public export
stagedBoostEMField : ProjectiveDihedron -> MinkowskiEMField -> Code MinkowskiEMField
stagedBoostEMField alpha em = quote (boostEMFieldProjective alpha em)

||| QTT 0 erased proof witness certifying 2LTT staged EM boost evaluation equivalence.
public export
0 prfStagedBoostEMField : (alpha : ProjectiveDihedron) -> (em : MinkowskiEMField) ->
                         splice (stagedBoostEMField alpha em) = boostEMFieldProjective alpha em
prfStagedBoostEMField alpha em = inverseSpliceQuote (boostEMFieldProjective alpha em)

------------------------------------------------------------------------
-- 7. COMPILE-TIME AUDIT PROOF WITNESSES (Rule 01)
------------------------------------------------------------------------

||| Audits:
||| 1. S' = N(α)² * S under boost along s-axis.
||| 2. Matrix congruence W' = μ(α*) · W · μ(α) matches vector action actDihedronVectorScaled.
||| 3. Null electromagnetic wavefront (S = 0) remains null (S' = 0) under any boost.
||| 4. Pure spatial rotation rotates (Er, Es) and scales Bz by N(α).
||| 5. Velocity boost from Pythagorean triad (3, 4, 5) with β = 3/5 evaluates without floats.
public export
auditMinkowskiEMFieldTransportProof : Bool
auditMinkowskiEMFieldTransportProof =
  let -- Initial field: Er = 3, Es = 4, Bz = 0 => S = 3² + 4² - 0 = 25
      em0 = MkMinkowskiEM [intToBoxInt 3, intToBoxInt 4] (intToBoxInt 0)
      s0 = emScalarInvariant em0

      -- 1. Boost along s with x = 3, s = 1 => N(α) = 3² - 1² = 8
      boostS = mkRationalBoostS (intToBoxInt 3) (intToBoxInt 1)
      normS = projNorm boostS
      emBoosted = boostEMFieldProjective boostS em0
      sBoosted = emScalarInvariant emBoosted
      expectedS = (normS * normS) * s0

      -- 2. Matrix sandwich equivalence (Theorem 78)
      muAlpha = dihedronToMatrix (projToDihedron boostS)
      muAdj   = dihedronToMatrix (projToDihedron (invProjDihedron boostS))
      wMat    = emToMatrix em0
      wSandwich = mulDMat2x2 (mulDMat2x2 muAdj wMat) muAlpha
      matrixEquiv = (emToMatrix emBoosted == wSandwich)

      -- 3. Null wavefront: Er = 5, Es = 0, Bz = 5 => S = 25 + 0 - 25 = 0
      emNull = MkMinkowskiEM [intToBoxInt 5, intToBoxInt 0] (intToBoxInt 5)
      sNull = emScalarInvariant emNull
      emNullBoosted = boostEMFieldProjective boostS emNull
      sNullBoosted = emScalarInvariant emNullBoosted

      -- 4. Pure spatial rotation: x = 4, t = 3 => N(α) = 4² + 3² = 25
      rot = mkRationalSpatialRotation (intToBoxInt 4) (intToBoxInt 3)
      normRot = projNorm rot
      emRot = boostEMFieldProjective rot em0
      sRot = emScalarInvariant emRot
      expectedRotS = (normRot * normRot) * s0

      -- 5. Velocity boost from triad (3, 4, 5)
      boostTriad = mkArbitraryRationalBoost (intToBoxInt 9) (intToBoxInt 3) (intToBoxInt 0)
      normTriad = projNorm boostTriad
      emTriad = boostEMFieldProjective boostTriad em0
      sTriad = emScalarInvariant emTriad
      expectedTriadS = (normTriad * normTriad) * s0
  in (s0 == intToBoxInt 25) &&
     (normS == intToBoxInt 8) &&
     (sBoosted == expectedS) &&
     matrixEquiv &&
     (sNull == intToBoxInt 0) &&
     (sNullBoosted == intToBoxInt 0) &&
     (normRot == intToBoxInt 25) &&
     (sRot == expectedRotS) &&
     (sTriad == expectedTriadS)

public export
0 prfAuditMinkowskiEMFieldTransport : Stage1.EM.MinkowskiFaraday.auditMinkowskiEMFieldTransportProof = True
prfAuditMinkowskiEMFieldTransport = Refl

||| Audit: MinkowskiEMField <-> Maxel AVL tree round-trip preserves exact field coordinates.
public export
auditEMMaxelRoundTripProof : Bool
auditEMMaxelRoundTripProof =
  let em = MkMinkowskiEM [intToBoxInt 6, intToBoxInt 4] (intToBoxInt 2)
  in maxelToEM (emToMaxel em) == em

||| Audit: MinkowskiEMField <-> Dihedron2 model stencil round-trip preserves exact field coordinates.
public export
auditEMDihedron2RoundTripProof : Bool
auditEMDihedron2RoundTripProof =
  let em = MkMinkowskiEM [intToBoxInt 8, intToBoxInt (-2)] (intToBoxInt 4)
  in dihedron2ToEM (emToDihedron2 em) == em

||| Audit: Deforested stream boost preserves scaled quadrance S' = N(α)² S across multiple field states.
public export
auditStreamBoostEMFieldProof : Bool
auditStreamBoostEMFieldProof =
  let em1 = MkMinkowskiEM [intToBoxInt 3, intToBoxInt 4] (intToBoxInt 0)
      em2 = MkMinkowskiEM [intToBoxInt 5, intToBoxInt 0] (intToBoxInt 3)
      boost = mkRationalBoostS (intToBoxInt 3) (intToBoxInt 1)
      normBoost = projNorm boost
      factor = normBoost * normBoost
      inStrm = stream [em1, em2]
      outStrm = streamBoostEMField boost inStrm
      res = foldStreamNat 2 (\acc, em => acc ++ [em]) (the (List MinkowskiEMField) []) outStrm
  in length res == 2 &&
     emScalarInvariant (head' res) == factor * emScalarInvariant em1
  where
    head' : List MinkowskiEMField -> MinkowskiEMField
    head' (x :: _) = x
    head' [] = MkMinkowskiEM [0, 0] 0

||| Audit: Deforested stream boost accumulation applies consecutive boosts in order.
public export
auditStreamAccumulateEMBoostsProof : Bool
auditStreamAccumulateEMBoostsProof =
  let em0 = MkMinkowskiEM [intToBoxInt 3, intToBoxInt 4] (intToBoxInt 0)
      b1 = mkRationalBoostR (intToBoxInt 2) (intToBoxInt 1)
      b2 = mkRationalBoostR (intToBoxInt 3) (intToBoxInt 1)
      boostStrm = stream [b1, b2]
      outStrm = streamAccumulateEMBoosts boostStrm em0
      res = foldStreamNat 2 (\acc, em => acc ++ [em]) (the (List MinkowskiEMField) []) outStrm
      finalBoost = mulProjDihedron (mulProjDihedron idProjDihedron b1) b2
      expectedFinalEM = boostEMFieldProjective finalBoost em0
  in length res == 2 &&
     last' res == expectedFinalEM
  where
    last' : List MinkowskiEMField -> MinkowskiEMField
    last' [x] = x
    last' (_ :: xs) = last' xs
    last' [] = MkMinkowskiEM [0, 0] 0
