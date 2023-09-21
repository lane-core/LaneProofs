{-# OPTIONS --safe --without-K --exact-split #-}

module ModularGroup.Properties where

open import MLTT.Spartan
open import MLTT.Unit-Properties

open import UF.Sets
open import UF.DiscreteAndSeparated
open import Groups.Type

open import ModularGroup.Type
open import ModularGroup.Composition
open import ModularGroup.Inversion

S-is-not-E : S ≠ E
S-is-not-E p = 𝟙-is-not-𝟘 (g (η-left-cancellable p))
  where
    f : (x : 𝓟) → 𝓤₀ ̇
    f 𝐸 = 𝟘
    f 𝑆 = 𝟙
    f (𝑠 x) = 𝟘

    g : 𝑆 ＝ 𝐸 → 𝟙 ＝ 𝟘
    g = ap f

η-is-not-θ : (x : 𝓟) (y : 𝓝) → η x ≠ θ y
η-is-not-θ x y p = 𝟙-is-not-𝟘 (g p)
  where
    f : 𝓜 → 𝓤₀ ̇
    f (η x) = 𝟙
    f (θ x) = 𝟘

    g : η x ＝ θ y → 𝟙 ＝ 𝟘
    g = ap f

θ-is-not-η : (x : 𝓝) (y : 𝓟) → θ x ≠ η y
θ-is-not-η x y p = η-is-not-θ y x (p ⁻¹)

fibers-of-η-over-E : (x : 𝓟) → is-decidable (η x ＝ E)
fibers-of-η-over-E 𝐸 = inl refl
fibers-of-η-over-E 𝑆 = inr S-is-not-E
fibers-of-η-over-E (𝑠 x) = inr (λ p → θ-is-not-η x 𝑆 (ap s p))

fibers-of-η-over-S : (x : 𝓟) → is-decidable (η x ＝ S)
fibers-of-η-over-S 𝐸 = inr (λ p → S-is-not-E (p ⁻¹))
fibers-of-η-over-S 𝑆 = inl refl
fibers-of-η-over-S (𝑠 x) = inr λ p → θ-is-not-η x 𝐸 (ap s p)

fibers-of-η-over-𝑠 : (x : 𝓟) (y : 𝓝) → is-decidable (η x ＝ η (𝑠 y))
fibers-of-θ-over-𝑟 : (x : 𝓝) (y : 𝓟) → is-decidable (θ x ＝ θ (𝑟 y))
fibers-of-θ-over-𝑟² : (x : 𝓝) (y : 𝓟) → is-decidable (θ x ＝ θ (𝑟² y))
η-is-decidable : (x y : 𝓟) → is-decidable (η x ＝ η y)
θ-is-decidable : (x y : 𝓝) → is-decidable (θ x ＝ θ y)

fibers-of-η-over-𝑠 𝐸 y = inr (𝟘-elim ∘ η-is-not-θ 𝑆 y ∘ ap s)
fibers-of-η-over-𝑠 𝑆 y = inr (𝟘-elim ∘ η-is-not-θ 𝐸 y ∘ ap s)
fibers-of-η-over-𝑠 (𝑠 x) y = 
  cases (inl ∘ ap s) (inr ∘ contrapositive s-left-cancellable) (θ-is-decidable x y)

fibers-of-θ-over-𝑟 (𝑟 x) y =
  cases (inl ∘ ap r) (inr ∘ contrapositive r-left-cancellable) (η-is-decidable x y)
fibers-of-θ-over-𝑟 (𝑟² x) y = inr (𝟘-elim ∘ η-is-not-θ x (𝑟² y) ∘ ap r)

fibers-of-θ-over-𝑟² (𝑟 x) y = inr (𝟘-elim ∘ η-is-not-θ x (𝑟 y) ∘ ap r²)
fibers-of-θ-over-𝑟² (𝑟² x) y = 
  cases (inl ∘ ap r²) (inr ∘ contrapositive r²-left-cancellable) (η-is-decidable x y)

η-is-decidable x 𝐸 = fibers-of-η-over-E x
η-is-decidable x 𝑆 = fibers-of-η-over-S x
η-is-decidable x (𝑠 y) = fibers-of-η-over-𝑠 x y

θ-is-decidable x (𝑟 y) = fibers-of-θ-over-𝑟 x y
θ-is-decidable x (𝑟² y) = fibers-of-θ-over-𝑟² x y

𝓜-is-discrete : is-discrete 𝓜
𝓜-is-discrete (η x) (η y) = η-is-decidable x y
𝓜-is-discrete (η x) (θ y) = inr (η-is-not-θ x y)
𝓜-is-discrete (θ x) (η y) = inr (≠-sym (η-is-not-θ y x))
𝓜-is-discrete (θ x) (θ y) = θ-is-decidable x y

𝓜-is-set : is-set 𝓜
𝓜-is-set = discrete-types-are-sets 𝓜-is-discrete

𝓜-has-monoid-structure : monoid-structure 𝓜
𝓜-has-monoid-structure = _·_ , E

𝓜-is-monoid : monoid-axioms 𝓜 𝓜-has-monoid-structure
𝓜-is-monoid = 𝓜-is-set , (λ x → refl)
            , composition-right-neutral
            , composition-associative

𝓜-has-group-structure : group-structure 𝓜
𝓜-has-group-structure = _·_

𝓜-is-group : group-axioms 𝓜 (_·_)
𝓜-is-group = 𝓜-is-set
           , composition-associative
           , E
           , (λ x → refl)
           , composition-right-neutral
           , 𝓜-invertible

PSL₂ℤ : Group 𝓤₀
PSL₂ℤ = 𝓜 , _·_ , 𝓜-is-group
