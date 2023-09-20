{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module ModularGroup.Type where

open import MLTT.Spartan
open import UF.Equiv

data 𝓟 : 𝓤₀ ̇
data 𝓝 : 𝓤₀ ̇

data 𝓝 where
  𝑟 : 𝓟 → 𝓝 -- R
  𝑟² : 𝓟 → 𝓝 -- R²

data 𝓟 where
  𝐸 : 𝓟
  𝑆 : 𝓟
  𝑠 : 𝓝 → 𝓟

data 𝓜 : 𝓤₀ ̇  where
  η : (x : 𝓟) → 𝓜
  θ : (x : 𝓝) → 𝓜

E S R R² : 𝓜
E = η 𝐸
S = η 𝑆
R = θ (𝑟 𝐸)
R² = θ (𝑟² 𝐸)

s r r² : 𝓜 → 𝓜
s (η 𝐸) = S
s (η 𝑆) = E
s (η (𝑠 x)) = θ x
s (θ x) = η (𝑠 x)
r (η x) = θ (𝑟 x)
r (θ (𝑟 x)) = θ (𝑟² x)
r (θ (𝑟² x)) = η x
r² x = r (r x)

s-quotiented : id ∼ s ∘ s
s-quotiented (η 𝐸) = refl
s-quotiented (η 𝑆) = refl
s-quotiented (η (𝑠 x)) = refl
s-quotiented (θ x) = refl

r-quotiented : id ∼ r ∘ r ∘ r
r-quotiented (η x) = refl
r-quotiented (θ (𝑟 x)) = refl
r-quotiented (θ (𝑟² x)) = refl

𝓜-induction : {A : 𝓜 → 𝓤 ̇ }
            → A E
            → ((X : 𝓜) → A X → A (s X))
            → ((X : 𝓜) → A X → A (r X))
            → (x : 𝓜) → A x
𝓜-induction base f g (η 𝐸) = base
𝓜-induction base f g (η 𝑆) = f (η 𝐸) base
𝓜-induction base f g (η (𝑠 x)) = f (θ x) (𝓜-induction base f g (θ x))
𝓜-induction base f g (θ (𝑟 x)) = g (η x) (𝓜-induction base f g (η x))
𝓜-induction base f g (θ (𝑟² x)) = g (θ (𝑟 x)) (g (η x) (𝓜-induction base f g (η x)))

𝓜-rec : (X : 𝓤 ̇ ) → X → (a b : 𝓜 → X → X) → 𝓜 → X
𝓜-rec X base a b x = 𝓜-induction base a b x

map : {X : 𝓤 ̇ } → X → (a b : X → X) → 𝓜 → X
map base a b (η 𝐸) = base
map base a b (η 𝑆) = a base
map base a b (η (𝑠 x)) = a (map base a b (θ x))
map base a b (θ (𝑟 x)) = b (map base a b (η x))
map base a b (θ (𝑟² x)) = b (b (map base a b (η x)))
