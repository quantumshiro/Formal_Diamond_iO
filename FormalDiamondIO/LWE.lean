import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic

noncomputable section

structure LWEParams where
  n: Nat -- dimension
  m: Nat -- sample size
  q: Nat -- modulus
  α: ℝ -- params for gaussian distribution

inductive LWEVariant
  | Search
  | Decision
  deriving Inhabited, BEq

-- Discrete Gaussian distribution
def DiscreteGaussian (q: Nat) [Fintype (ZMod q)] [DecidableEq (ZMod q)] (α: ℝ) : Type :=
  { D: (ZMod q) → ℝ //
    (∀ x, 0 ≤ D x) ∧
    (∑ x, D x) = 1
  }

def SampleGaussian (q: Nat) (α: ℝ) : Type :=
  Unit → ZMod q

namespace LWE
def ZMod.lift {q: Nat} (x: ZMod q) : Int :=
  let val := x.val
  if val > q / 2 then val - q else val
end LWE

def standardLWEParams : LWEParams :=
  { n := 256, m := 512, q := 7681, α := 0.005 }
