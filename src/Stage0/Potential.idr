module Stage0.Potential

import Stage0.BoxInt
import Stage1.VexelMaxel
import public Stage1.GrassmannCalculus
import Data.List

%default total

------------------------------------------------------------------------
-- 1. DISCRETE ELECTROMAGNETIC POTENTIAL FIELDS (0-FORM & 1-FORM)
------------------------------------------------------------------------

||| Scalar Electric Potential Field Phi (0-Form Cochain over Vexel singletons).
public export
ElectricPotential : Type
ElectricPotential = PointCochain

||| Magnetic Vector Potential Field A (1-Form Cochain over Maxel directed edge pixels).
public export
VectorPotential : Type
VectorPotential = EdgeCochain

||| Initialized vacuum scalar potential field (Phi = 0).
public export
vacuumElectricPotential : ElectricPotential
vacuumElectricPotential = MkVexel []

||| Initialized vacuum vector potential field (A = 0).
public export
vacuumVectorPotential : VectorPotential
vacuumVectorPotential = MkMaxel []

||| Evaluates discrete scalar potential Phi at a given vertex node Unixel.
public export
evaluateScalarPotentialAt : Unixel -> ElectricPotential -> BoxInt
evaluateScalarPotentialAt node phi = lookupPoint node phi

||| Evaluates discrete gauge connection A along a directed edge tuple (u -> v).
public export
evaluateVectorPotentialAt : (Unixel, Unixel) -> VectorPotential -> BoxInt
evaluateVectorPotentialAt edge a = lookupEdge edge a

||| Superposes two scalar electric potential fields (Phi_1 + Phi_2).
public export
superposeElectricPotentials : ElectricPotential -> ElectricPotential -> ElectricPotential
superposeElectricPotentials phi1 phi2 = addVexel phi1 phi2

||| Superposes two vector magnetic potential fields (A_1 + A_2).
public export
superposeVectorPotentials : VectorPotential -> VectorPotential -> VectorPotential
superposeVectorPotentials a1 a2 = addMaxel a1 a2

||| Scales a scalar electric potential field by an integer charge factor k.
public export
scaleElectricPotential : BoxInt -> ElectricPotential -> ElectricPotential
scaleElectricPotential k phi = scaleVexel k phi

||| Scales a magnetic vector potential field by an integer coupling factor k.
public export
scaleVectorPotential : BoxInt -> VectorPotential -> VectorPotential
scaleVectorPotential k a = scaleMaxel k a
