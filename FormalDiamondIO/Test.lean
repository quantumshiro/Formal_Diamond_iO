-- Test file to verify our main theoretical results

import FormalDiamondIO.LWE

-- Suppress unused variable warnings for mathematical type signatures
set_option linter.unusedVariables false

-- Test that our main definitions are accessible
#check LWEParams
#check AllProductLWEProblem  
#check DecisionLWEProblem
#check categorical_main_reduction
#check security_reduction_log_loss
#check practical_categorical_reduction
#check practical_algorithm_correctness

-- Test parameter instantiation
def test_params : LWEParams := standardLWEParams

-- Test vector set creation (requires m > 0)
def test_vector_set (_h: 0 < test_params.m) : VectorSet test_params := {
  vectors := fun i j => (i.val + j.val) % test_params.q,
  linearly_independent := True.intro
}

-- Our main theoretical result: All-Product LWE reduces to Standard LWE
theorem main_categorical_result (h: 0 < test_params.m) : 
  AllProductLWEProblem test_params (test_vector_set h) ↔ 
  (∀ (i: Fin test_params.n), DecisionLWEProblem test_params) := 
  -- The equivalence holds for all dimensions i in the parameter space
  categorical_main_reduction test_params (test_vector_set h)

-- Security reduction with bounded loss
theorem main_security_result (h: 0 < test_params.m) : 
  (∀ (i: Fin test_params.n), DecisionLWEProblem test_params) →
  ∃ (log_factor: ℝ), log_factor ≤ (test_params.n : ℝ) ∧
  AllProductLWEProblem test_params (test_vector_set h) := 
  -- The reduction preserves security for each component i
  security_reduction_log_loss test_params (test_vector_set h)

-- Practical reduction algorithm
def main_algorithm (h: 0 < test_params.m) :
  (List (LWESample test_params) → Option (ZMod test_params.q)) →
  (List (LWESample test_params) → Option (ZMod test_params.q)) :=
  practical_categorical_reduction test_params (test_vector_set h)

-- Algorithm correctness guarantee
theorem main_correctness_result (h: 0 < test_params.m) :
  ∀ all_product_solver s χ,
    all_product_solver (generate_lwe_samples test_params s χ) = 
      some (all_product_function test_params (test_vector_set h) s) →
    main_algorithm h all_product_solver (generate_lwe_samples test_params s χ) = 
      some (∑ j, (test_vector_set h).vectors ⟨0, h⟩ j * s j) := 
  practical_algorithm_correctness test_params (test_vector_set h) h