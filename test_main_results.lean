-- Test file to verify our main theoretical results

import FormalDiamondIO.LWE

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
def test_vector_set (h: 0 < test_params.m) : VectorSet test_params := {
  vectors := fun i j => (i.val + j.val) % test_params.q,
  linearly_independent := True.intro
}

-- Verify our main theoretical result is accessible
example (h: 0 < test_params.m) : 
  AllProductLWEProblem test_params (test_vector_set h) ↔ 
  (∀ (i: Fin test_params.n), DecisionLWEProblem test_params) := 
  categorical_main_reduction test_params (test_vector_set h)

-- Verify security reduction result
example (h: 0 < test_params.m) : 
  (∀ (i: Fin test_params.n), DecisionLWEProblem test_params) →
  ∃ (log_factor: ℝ), log_factor ≤ (test_params.n : ℝ) ∧
  AllProductLWEProblem test_params (test_vector_set h) := 
  security_reduction_log_loss test_params (test_vector_set h)

-- Verify the practical algorithm exists
example (h: 0 < test_params.m) :
  (List (LWESample test_params) → Option (ZMod test_params.q)) →
  (List (LWESample test_params) → Option (ZMod test_params.q)) :=
  practical_categorical_reduction test_params (test_vector_set h)

#print "✅ All main theoretical results are properly defined and accessible!"