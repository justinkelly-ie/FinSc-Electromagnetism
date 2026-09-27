module Main

import QuickCheck
import Data.List
import Stage0.Multiset
import Stage0.BoxInt
import Stage0.Pixel
import Stage0.Interfaces
import Substrate.Core
import Substrate.Difference
import Substrate.Divergence
import Substrate.Laplacian
import Substrate.Hodge
import EM.Potential
import EM.Flux
import EM.Gauge
import EM.Calculus
import EM.Hodge

%default total

--------------------------------------------------------------------------------
-- 1. ARBITRARY INSTANCES
--------------------------------------------------------------------------------

public export
Arbitrary BoxInt where
  arbitrary = do
    n <- arbitrary {a=Integer}
    pure (fromInteger n)
  coarbitrary b gen =
    let (Math.Interfaces.MkUr val) = boxToInt b
    in coarbitrary val gen

public export
Arbitrary Geometry where
  arbitrary = do
    x <- arbitrary {a=BoxInt}
    y <- arbitrary {a=BoxInt}
    pure (MkPixel x y)
  coarbitrary (MkPixel x y) gen =
    coarbitrary x (coarbitrary y gen)

public export
Show Plaquette where
  show (MkPlaquette p1 p2 p3 p4) = "Plaquette"

public export
Arbitrary Plaquette where
  arbitrary = do
    g1 <- arbitrary {a=Geometry}
    g2 <- arbitrary {a=Geometry}
    g3 <- arbitrary {a=Geometry}
    g4 <- arbitrary {a=Geometry}
    pure (MkPlaquette g1 g2 g3 g4)
  coarbitrary (MkPlaquette g1 g2 g3 g4) gen =
    coarbitrary g1 (coarbitrary g2 (coarbitrary g3 (coarbitrary g4 gen)))

--------------------------------------------------------------------------------
-- 2. DEFINITION TESTS: POTENTIAL, GAUGE & FLUX ALGEBRA
--------------------------------------------------------------------------------

||| Vacuum potential and substrate yield empty gauge field: A_ij = 0
prop_gaugeFieldVacuum : Property
prop_gaugeFieldVacuum = forAll {a = Bool} {prop = Bool} arbitrary (MkFn (\_ =>
  computeGaugeField emptyVexel emptySubstrate == emptySubstrate))

||| Empty plaquette flux is 0: B = ∮ A · dl = 0
prop_plaquetteFluxVacuum : Property
prop_plaquetteFluxVacuum = forAll {a = Plaquette} {prop = Bool} arbitrary (MkFn (\plaq =>
  computePlaquetteFlux plaq emptySubstrate == 0))

||| Empty Maxel gauge operator is an isometry permutation
prop_permutationMaxelVacuum : Property
prop_permutationMaxelVacuum = forAll {a = Bool} {prop = Bool} arbitrary (MkFn (\_ =>
  isPermutationMaxel emptySubstrate == True))

||| Applying gauge maxel operator to vacuum state yields vacuum
prop_applyGaugeMaxelVacuum : Property
prop_applyGaugeMaxelVacuum = forAll {a = Bool} {prop = Bool} arbitrary (MkFn (\_ =>
  applyGaugeMaxel emptySubstrate emptyVexel == emptyVexel))

--------------------------------------------------------------------------------
-- 3. PROPERTY TESTS: DISCRETE MAXWELL CALCULUS & GAUGE INVARIANCE
--------------------------------------------------------------------------------

||| Electric field divergence on vacuum gauge field yields empty vexel (∇ · E = 0)
prop_electricDivergenceVacuum : Property
prop_electricDivergenceVacuum = forAll {a = Bool} {prop = Bool} arbitrary (MkFn (\_ =>
  computeElectricDivergence emptySubstrate == emptyVexel))

||| Potential Laplacian on vacuum potential yields empty vexel (Δ Φ = 0)
prop_potentialLaplacianVacuum : Property
prop_potentialLaplacianVacuum = forAll {a = Bool} {prop = Bool} arbitrary (MkFn (\_ =>
  computePotentialLaplacian emptyVexel emptySubstrate == emptyVexel))

||| Hodge decomposition of vacuum EM field produces harmonic vacuum components
prop_decomposeEMFieldVacuum : Property
prop_decomposeEMFieldVacuum = forAll {a = Bool} {prop = Bool} arbitrary (MkFn (\_ =>
  let (MkHodge harm grad curl) = decomposeEMField emptyVexel emptySubstrate
  in harm == emptyVexel && grad == emptyVexel && curl == emptyVexel))

||| Gauge Invariance: Constant potential shift Φ → Φ + c leaves gauge field A_ij = Φ_j - Φ_i invariant
prop_gaugeInvarianceConstantShift : Property
prop_gaugeInvarianceConstantShift = forAll {a = (Geometry, Geometry)} {prop = Bool} arbitrary (MkFn (\(g1, g2) =>
  let sub = singleEdge g1 g2
      -- Constant potential across all nodes
      phiConst = superposeStates (singletonVexel g1 (posTerm 0 0 5)) (singletonVexel g2 (posTerm 0 0 5))
      gaugeField = computeGaugeField phiConst sub
      -- Difference (5 - 5 = 0)
  in gaugeField == fromList [((g1, g2), 0)]))

--------------------------------------------------------------------------------
-- 4. TEST RUNNER
--------------------------------------------------------------------------------

partial
runSuite : IO ()
runSuite = do
  putStrLn ""
  putStrLn "--------------------------------------------------------"
  putStrLn "-- idris2-Electromagnetism: Maxwell Field Test Suite --"
  putStrLn "--------------------------------------------------------"
  putStrLn ""

  let r1 = quickCheck prop_gaugeFieldVacuum
  putStrLn $ "prop_gaugeFieldVacuum: " ++ r1.msg

  let r2 = quickCheck prop_plaquetteFluxVacuum
  putStrLn $ "prop_plaquetteFluxVacuum: " ++ r2.msg

  let r3 = quickCheck prop_permutationMaxelVacuum
  putStrLn $ "prop_permutationMaxelVacuum: " ++ r3.msg

  let r4 = quickCheck prop_applyGaugeMaxelVacuum
  putStrLn $ "prop_applyGaugeMaxelVacuum: " ++ r4.msg

  let r5 = quickCheck prop_electricDivergenceVacuum
  putStrLn $ "prop_electricDivergenceVacuum: " ++ r5.msg

  let r6 = quickCheck prop_potentialLaplacianVacuum
  putStrLn $ "prop_potentialLaplacianVacuum: " ++ r6.msg

  let r7 = quickCheck prop_decomposeEMFieldVacuum
  putStrLn $ "prop_decomposeEMFieldVacuum: " ++ r7.msg

  let r8 = quickCheck prop_gaugeInvarianceConstantShift
  putStrLn $ "prop_gaugeInvarianceConstantShift: " ++ r8.msg

  let results = [r1, r2, r3, r4, r5, r6, r7, r8]
  let failures = filter (\r => isJust r.pass && fromMaybe True r.pass == False) results
  if null failures
    then putStrLn "\nAll 8 Electromagnetism tests passed."
    else idris_crash "❌ FAILURE: One or more Electromagnetism properties failed verification."

partial
main : IO ()
main = runSuite
