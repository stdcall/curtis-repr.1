import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

/- Bounded checks for Lemma 3.17 and Theorem 2.19.
Schur's argument is for arbitrary simple left modules over a ring.
The adjunction is the commutative specialization A = B = K; it does not
formalize the full noncommutative bimodule hypotheses of the book. -/
namespace CurtisReinerI

theorem schur_bijective {R M N : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [IsSimpleModule R M] [IsSimpleModule R N]
    (f : M →ₗ[R] N) (hf : f ≠ 0) : Function.Bijective f := by
  constructor
  · rcases eq_bot_or_eq_top f.ker with h | h
    · exact LinearMap.ker_eq_bot.mp h
    · exact False.elim (hf (LinearMap.ker_eq_top.mp h))
  · rcases eq_bot_or_eq_top f.range with h | h
    · exact False.elim (hf (LinearMap.range_eq_bot.mp h))
    · exact LinearMap.range_eq_top.mp h

theorem schur_inverse {R M : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [IsSimpleModule R M]
    (f : Module.End R M) (hf : f ≠ 0) :
    ∃ g : Module.End R M, g * f = 1 ∧ f * g = 1 := by
  classical
  let e := LinearEquiv.ofBijective f (schur_bijective f hf)
  refine ⟨e.symm.toLinearMap, ?_, ?_⟩
  · ext x
    change e.symm (e x) = x
    exact e.symm_apply_apply x
  · ext x
    change e (e.symm x) = x
    exact e.apply_symm_apply x

noncomputable section
open TensorProduct
variable {K L M N : Type*} [CommRing K]
  [AddCommGroup L] [Module K L] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N]

def tau (f : L →ₗ[K] M →ₗ[K] N) : M ⊗[K] L →ₗ[K] N :=
  TensorProduct.lift f.flip

def curry (g : M ⊗[K] L →ₗ[K] N) : L →ₗ[K] M →ₗ[K] N :=
  ((TensorProduct.mk K M L).compr₂ g).flip

theorem tau_evaluation (f : L →ₗ[K] M →ₗ[K] N) (m : M) (l : L) :
    tau f (m ⊗ₜ[K] l) = f l m := by
  rfl

theorem curry_tau (f : L →ₗ[K] M →ₗ[K] N) : curry (tau f) = f := by
  ext l m
  rfl

theorem tau_curry (g : M ⊗[K] L →ₗ[K] N) : tau (curry g) = g := by
  apply TensorProduct.ext'
  intro m l
  rfl

end
end CurtisReinerI

#print axioms CurtisReinerI.schur_bijective
#print axioms CurtisReinerI.schur_inverse
#print axioms CurtisReinerI.tau_evaluation
#print axioms CurtisReinerI.curry_tau
#print axioms CurtisReinerI.tau_curry
