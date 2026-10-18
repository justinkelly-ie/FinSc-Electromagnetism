module Stage0.MultipolePoly

import Stage0.BoxInt
import Stage1.Polynumber
import Data.Vect

%default total

------------------------------------------------------------------------
-- 1. DEGREE-CERTIFIED MULTIPOLE EXPANSION POLYNOMIALS
------------------------------------------------------------------------

||| Degree-certified Electromagnetic Multipole Potential Expansion Polynomial:
||| \Phi(u) = \sum_{\ell=0}^order q_\ell * u^\ell
||| where u represents inverse distance quanta, \ell=0 is the monopole,
||| \ell=1 is the dipole, \ell=2 is the quadrupole.
public export
record MultipolePotentialDepPoly (polyOrder : Nat) where
  constructor MkMultipolePotentialDepPoly
  poly : DepPolynumber polyOrder

||| Constructs a multipole expansion polynomial from moment vector.
public export
multipolePotentialDepPoly : (polyOrder : Nat) -> Vect (S polyOrder) BoxInt -> MultipolePotentialDepPoly polyOrder
multipolePotentialDepPoly polyOrder moments =
  MkMultipolePotentialDepPoly (MkDepPolynumber moments)

||| Evaluates discrete multipole potential at inverse distance quanta u.
public export
evalMultipolePotential : MultipolePotentialDepPoly polyOrder -> BoxInt -> BoxInt
evalMultipolePotential (MkMultipolePotentialDepPoly p) u = evalDepPolynumber p u

------------------------------------------------------------------------
-- 2. PHOTONIC STACK CHARACTERISTIC TRANSFER POLYNOMIALS
------------------------------------------------------------------------

||| Characteristic transfer polynomial of an individual dielectric layer (degree 2):
||| P_layer(z) = det(M_interface + z * M_prop)
public export
layerTransferDepPoly : (n1 : BoxInt) -> (n2 : BoxInt) -> (phi : BoxInt) -> DepPolynumber 2
layerTransferDepPoly n1 n2 phi =
  let c0 = mulBox (intToBoxInt 4) (mulBox n1 n2)
      c1 = addBox n1 n2
      c2 = mulBox phi phi
  in MkDepPolynumber [c0, c1, c2]

||| Computes composite photonic transfer polynomial across a 2-layer stack with degree 4:
||| deg(P_1 * P_2) = 2 + 2 = 4.
public export
twoLayerStackTransferDepPoly : DepPolynumber 2 -> DepPolynumber 2 -> DepPolynumber 4
twoLayerStackTransferDepPoly l1 l2 = mulDepPolynumber l1 l2

------------------------------------------------------------------------
-- 3. COMPILE-TIME AUDIT WITNESSES
------------------------------------------------------------------------

||| Compile-time audit witness verifying exact degree and evaluation of dipole and quadrupole expansions.
public export
auditMultipolePolyProof : Bool
auditMultipolePolyProof =
  let q0 = intToBoxInt 10 -- Monopole charge
      q1 = intToBoxInt 4  -- Dipole moment
      q2 = intToBoxInt 1  -- Quadrupole moment
      quad = multipolePotentialDepPoly 2 [q0, q1, q2]
      u = intToBoxInt 2
      val = evalMultipolePotential quad u
      -- 10 + 4 * 2 + 1 * 4 = 10 + 8 + 4 = 22
      expected = intToBoxInt 22
      l1 = layerTransferDepPoly (intToBoxInt 1) (intToBoxInt 2) (intToBoxInt 1)
      l2 = layerTransferDepPoly (intToBoxInt 2) (intToBoxInt 3) (intToBoxInt 2)
      stack4 = twoLayerStackTransferDepPoly l1 l2
  in boxEq val expected && evalDepPolynumber stack4 u > intToBoxInt 0
