module Stage1.Reflect.Auditor.EM

import public Language.Reflection
import Stage0.BoxInt
import Stage1.VexelMaxel
import public Stage0.Potential
import public Stage1.EM.Calculus
import public Stage1.EM.Gauge
import public Stage0.Flux
import public Stage1.EM.Hodge
import public Stage1.EM.Maxwell

%default total

------------------------------------------------------------------------
-- 1. CONSTRUCTIVE PHYSICAL INVARIANT WITNESSES
------------------------------------------------------------------------

public export
auditEMConstantPotentialProofExport : Bool
auditEMConstantPotentialProofExport = auditConstantPotentialZeroFieldProof

public export
auditEMGaugeInvarianceProofExport : Bool
auditEMGaugeInvarianceProofExport = auditGaugeInvarianceProof

public export
auditEMNoMonopolesProofExport : Bool
auditEMNoMonopolesProofExport = auditNoMagneticMonopolesProof

public export
auditEMHodgeInvolutionProofExport : Bool
auditEMHodgeInvolutionProofExport = EM.Hodge.auditHodgeStarInvolutionProof

public export
auditEMVacuumMaxwellProofExport : Bool
auditEMVacuumMaxwellProofExport = auditMaxwellVacuumSolenoidProof

------------------------------------------------------------------------
-- 2. ELABORATOR REFLECTION MACROS (RULE 01)
------------------------------------------------------------------------

||| Universal compile-time invariant auditing macro tactic for Electromagnetism.
public export
%macro
auditEMInvariant : (prop : Bool) -> Elab (prop = True)
auditEMInvariant True = pure Refl
auditEMInvariant False = fail "Compile-time EM invariant audit failed!"
