module ModularGroup.Inversion where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv

open import ModularGroup.Type
open import ModularGroup.Composition

_^⁻¹ : 𝓜 → 𝓜
η 𝐸 ^⁻¹ = E
η 𝑆 ^⁻¹ = S
η (𝑠 x) ^⁻¹ = θ x ^⁻¹ · S
θ (𝑟 x) ^⁻¹ = η x ^⁻¹ · R²
θ (𝑟² x) ^⁻¹ = η x ^⁻¹ · R

s-inverse : (x : 𝓜) → (s x) ^⁻¹ ＝ x ^⁻¹ · S
s-inverse (η 𝐸) = refl
s-inverse (η 𝑆) = refl
s-inverse (η (𝑠 x)) = composition-right-neutral (θ x ^⁻¹) ⁻¹
                    ∙ composition-associative (θ x ^⁻¹) (η 𝑆) (η 𝑆) ⁻¹
s-inverse (θ x) = refl

r-inverse : (x : 𝓜) → (r x) ^⁻¹ ＝ x ^⁻¹ · R²
r-inverse (η 𝐸) = refl
r-inverse (η 𝑆) = refl
r-inverse (η (𝑠 x)) = refl
r-inverse (θ (𝑟 x)) = composition-associative (η x ^⁻¹) (θ (𝑟² 𝐸)) (θ (𝑟² 𝐸)) ⁻¹
r-inverse (θ (𝑟² x)) = composition-right-neutral (η x ^⁻¹) ⁻¹
                     ∙ composition-associative (η x ^⁻¹) (θ (𝑟 𝐸)) (θ (𝑟² 𝐸)) ⁻¹

r²-inverse : (x : 𝓜) → (r² x) ^⁻¹ ＝ x ^⁻¹ · R
r²-inverse (η x) = refl
r²-inverse (θ (𝑟 𝐸)) = refl
r²-inverse (θ (𝑟 𝑆)) = refl
r²-inverse (θ (𝑟 (𝑠 x))) = composition-right-neutral ((θ x ^⁻¹) · η 𝑆) ⁻¹
                         ∙ composition-associative ((θ x ^⁻¹) · η 𝑆) (θ (𝑟² 𝐸)) (θ (𝑟 𝐸)) ⁻¹
r²-inverse (θ (𝑟² x)) = composition-associative (η x ^⁻¹) (θ (𝑟 𝐸)) (θ (𝑟 𝐸)) ⁻¹


s-inverse-right : (x : 𝓜) → (x · S) ^⁻¹ ＝ s (x ^⁻¹)
r-inverse-right : (x : 𝓜) → (x · R²) ^⁻¹ ＝ r (x ^⁻¹)
r²-inverse-right : (x : 𝓜) → (x · R) ^⁻¹ ＝ r² (x ^⁻¹)

s-inverse-right (η 𝐸) = refl
s-inverse-right (η 𝑆) = refl
s-inverse-right (η (𝑠 x)) = s-inverse (θ x · η 𝑆)
                          ∙ ap (_· S) (s-inverse-right (θ x))
                          ∙ composition-associative (η 𝑆) (θ x ^⁻¹) (η 𝑆)
s-inverse-right (θ (𝑟 x)) = r-inverse (η x · η 𝑆)
                          ∙ ap (_· R²) (s-inverse-right (η x))
                          ∙ composition-associative (η 𝑆) (η x ^⁻¹) (θ (𝑟² 𝐸))
s-inverse-right (θ (𝑟² x)) = r²-inverse (η x · η 𝑆)
                           ∙ ap (_· R) (s-inverse-right (η x))
                           ∙ composition-associative (η 𝑆) (η x ^⁻¹) (θ (𝑟 𝐸))

r-inverse-right (η x) = ?
r-inverse-right (θ x) = ?
r²-inverse-right x = {!!}

inverse-left-cancel : (x : 𝓜) → x ^⁻¹ · x ＝ E
inverse-left-cancel (η 𝐸) = refl
inverse-left-cancel (η 𝑆) = refl
inverse-left-cancel (η (𝑠 x)) = composition-associative (θ x ^⁻¹) (η 𝑆) (η (𝑠 x))
                              ∙ inverse-left-cancel (θ x)
inverse-left-cancel (θ (𝑟 x)) = composition-associative (η x ^⁻¹) (θ (𝑟² 𝐸)) (θ (𝑟 x))
                              ∙ ap ((η x ^⁻¹) ·_) (r-quotiented (η x) ⁻¹)
                              ∙ inverse-left-cancel (η x)
inverse-left-cancel (θ (𝑟² x)) = composition-associative (η x ^⁻¹) (θ (𝑟 𝐸)) (θ (𝑟² x))
                               ∙ inverse-left-cancel (η x)

inverse-right-cancel : (x : 𝓜) → x · x ^⁻¹ ＝ E
inverse-right-cancel (η 𝐸) = refl
inverse-right-cancel (η 𝑆) = refl
inverse-right-cancel (η (𝑠 x)) =
  ap s (composition-associative (θ x) (θ x ^⁻¹) (η 𝑆) ⁻¹)
  ∙ ap (λ u → s (u · η 𝑆)) (inverse-right-cancel (θ x))
inverse-right-cancel (θ (𝑟 x)) = 
  ap r (composition-associative (η x) (η x ^⁻¹) (θ (𝑟² 𝐸)) ⁻¹)
  ∙ ap (λ u → r (u · R²)) (inverse-right-cancel (η x))
inverse-right-cancel (θ (𝑟² x)) = 
  ap r² (composition-associative (η x) (η x ^⁻¹) (θ (𝑟 𝐸)) ⁻¹)
  ∙ ap (λ u → r² (u · R)) (inverse-right-cancel (η x))


𝓜-invertible : (x : 𝓜) → Σ x' ꞉ 𝓜 , (x' · x ＝ E) × (x · x' ＝ E)
𝓜-invertible x = x ^⁻¹ , inverse-left-cancel x , inverse-right-cancel x



inversion-injective-η : (x y : 𝓟) → (η x) ^⁻¹ ＝ (η y) ^⁻¹ → η x ＝ η y
inversion-injective-η 𝐸 y p = {!!}
inversion-injective-η 𝑆 y p = {!!}
inversion-injective-η (𝑠 x) y p = {!!}

inversion-injective-θ : (x y : 𝓝) → (θ x) ^⁻¹ ＝ (θ y) ^⁻¹ → (θ x) ＝ (θ y)
inversion-injective-θ x y p = {!!}

inversion-injective : (x y : 𝓜) → x ^⁻¹ ＝ y ^⁻¹ → x ＝ y
inversion-injective (η 𝐸) (η y) p = {!!}
inversion-injective (η 𝑆) (η y) p = {!!}
inversion-injective (η (𝑠 x)) (η y) p = {!!}
inversion-injective (η x) (θ y) p = {!!}
inversion-injective (θ x) y p = {!!}

inverse-involutive-η : (x : 𝓟) → (η x ^⁻¹) ^⁻¹ ＝ η x
inverse-involutive-η 𝐸 = refl
inverse-involutive-η 𝑆 = refl
inverse-involutive-η (𝑠 x) = (((θ x ^⁻¹) · η 𝑆) ^⁻¹) ＝⟨ I ⟩
                             (((θ x ^⁻¹) · η 𝑆) ^⁻¹) ＝⟨ {!!} ⟩
                             η (𝑠 x) ∎
  where
    I : ((θ x ^⁻¹) · S) ^⁻¹ ＝ (((θ x ^⁻¹) · η 𝑆) ^⁻¹)
    I = ap (_^⁻¹) (s-inverse (θ x) ⁻¹)


inverse-involutive-θ : (x : 𝓝) → (θ x ^⁻¹) ^⁻¹ ＝ θ x
inverse-involutive-θ (𝑟 x) = {!!}
inverse-involutive-θ (𝑟² x) = {!!}

inverse-involutive : (x : 𝓜) → x ＝ (x ^⁻¹) ^⁻¹
inverse-involutive (η 𝐸) = refl
inverse-involutive (η 𝑆) = refl
inverse-involutive (η (𝑠 x)) = {!!}
inverse-involutive (θ (𝑟 x)) = {!!}
inverse-involutive (θ (𝑟² x)) = {!!}
