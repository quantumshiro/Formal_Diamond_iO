import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic

noncomputable section

structure LWEParams where
  n: Nat -- dimension
  m: Nat -- sample size
  q: Nat -- modulus
  α: ℝ -- params for gaussian distribution

-- Discrete Gaussian distribution
def DiscreteGaussian (q: Nat) [Fintype (ZMod q)] [DecidableEq (ZMod q)] (α: ℝ) : Type :=
  { D: (ZMod q) → ℝ //
    (∀ x, 0 ≤ D x) ∧
    (∑ x, D x) = 1
  }
