{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

open import UF.FunExt

module TernaryIntegers.Type where

open import MLTT.Spartan renaming (_+_ to _∔_)

open import UF.Base
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.FunExt
open import UF.Embeddings
open import UF.Equiv
open import UF.Retracts

data 𝕋 : 𝓤₀ ̇  where
  one : 𝕋
  L : 𝕋 → 𝕋 -- 3x-1
  T : 𝕋 → 𝕋 -- 3x
  R : 𝕋 → 𝕋 -- 3x+1

data ℤ : 𝓤₀ ̇  where
  zero : ℤ
  pos : (x : 𝕋) → ℤ
  neg : (x : 𝕋) → ℤ

𝕋-induction : {A : 𝕋 → 𝓤 ̇ }
            → A one
            → ((s : 𝕋) → A s → A (L s))
            → ((s : 𝕋) → A s → A (T s))
            → ((s : 𝕋) → A s → A (R s))
            → (t : 𝕋) → A t
𝕋-induction base f g h one = base
𝕋-induction base f g h (L t) = f t (𝕋-induction base f g h t)
𝕋-induction base f g h (T t) = g t (𝕋-induction base f g h t)
𝕋-induction base f g h (R t) = h t (𝕋-induction base f g h t)

-- parity
open import MLTT.Plus-Properties

even𝕋 odd𝕋 : 𝕋 → 𝓤₀ ̇
even𝕋 one = 𝟘
even𝕋 (L x) = odd𝕋 x
even𝕋 (T x) = even𝕋 x
even𝕋 (R x) = odd𝕋 x
odd𝕋 one = 𝟙
odd𝕋 (L x) = even𝕋 x
odd𝕋 (T x) = odd𝕋 x
odd𝕋 (R x) = even𝕋 x

div2 : Σ t ꞉ 𝕋 , even𝕋 t → 𝕋
div2 (L t , l) = {!!}
div2 (T t , l) = T (div2 (t , l))
div2 (R t , l) = {!!}

parity-split : (x : 𝕋) → odd𝕋 x ∔ even𝕋 x
parity-split one = inl ⋆
parity-split (L x) = +-commutative (parity-split x)
parity-split (T x) = parity-split x
parity-split (R x) = +-commutative (parity-split x)

--collatz-split : 𝕋 → 𝕋
--collatz-split x = cases (λ _ → R x) (λ _ → x) (parity-split x)
--
--collatz-step : 𝕋 → 𝕋
--collatz-step x = cases (λ o → {!!}) (λ e → {!!}) (parity-split x)
--
--collatz : 𝕋 → 𝓤 ̇
--collatz x = cases (λ _ → collatz (R x)) {!!} (parity-split x)

---- abs
--triple𝕋 : 𝕋 → ℕ
--triple𝕋 one = succ (succ (succ zero))
--triple𝕋 (L one) = {!!}
--triple𝕋 (L (L x)) = {!!}
--triple𝕋 (L (T x)) = {!!}
--triple𝕋 (L (R x)) = {!!}
--triple𝕋 (T x) = {!!}
--triple𝕋 (R x) = {!!}
--
--abs-pred𝕋 : 𝕋 → ℕ
--abs-pred𝕋 one = zero
--abs-pred𝕋 (L one) = succ zero
--abs-pred𝕋 (L (L x)) = {!!}
--abs-pred𝕋 (L (T x)) = {!!}
--abs-pred𝕋 (L (R x)) = {!!}
--abs-pred𝕋 (T one) = succ (succ zero)
--abs-pred𝕋 (T (L x)) = {!!}
--abs-pred𝕋 (T (T x)) = {!!}
--abs-pred𝕋 (T (R x)) = {!!}
--abs-pred𝕋 (R x) = {!succ (succ (abs𝕋 (L x)))!}
--
--abs : ℤ → ℕ
--abs zero = zero
--abs (pos x) = {!!}
--abs (neg x) = {!!}

ll : ℤ → ℤ
ll zero = neg one
ll (pos x) = pos (L x)
ll (neg x) = neg (R x)

tt : ℤ → ℤ
tt zero = zero
tt (pos x) = pos (T x)
tt (neg x) = neg (T x)

rr : ℤ → ℤ
rr zero = pos one
rr (pos x) = pos (R x)
rr (neg x) = neg (L x)

-_ : ℤ → ℤ
- zero = zero
- pos x = neg x
- neg x = pos x

succ𝕋 : 𝕋 → 𝕋
succ𝕋 one = L one
succ𝕋 (L t) = T t
succ𝕋 (T t) = R t
succ𝕋 (R t) = L (succ𝕋 t)

succℤ predℤ : ℤ → ℤ
succℤ zero = pos one
succℤ (pos x) = pos (succ𝕋 x)
succℤ (neg one) = zero
succℤ (neg (L x)) = ll (succℤ (neg x))
succℤ (neg (T x)) = rr (neg x) -- 1 + (-3x) = - (3x - 1)
succℤ (neg (R x)) = tt (neg x) -- 1 + -(3x+1) = -3x

predℤ zero = neg one
predℤ (pos one) = zero
predℤ (pos (L x)) = rr (predℤ (pos x)) -- (3x - 2) = 3(x-1) + 1
predℤ (pos (T x)) = ll (pos x)
predℤ (pos (R x)) = pos (T x)
predℤ (neg x) = neg (succ𝕋 x)

succℤ-rr : (z : ℤ) → succℤ (rr z) ＝ ll (succℤ z)
succℤ-rr zero = refl
succℤ-rr (pos x) = refl
succℤ-rr (neg x) = refl

predℤ-ll : (z : ℤ) → predℤ (ll z) ＝ rr (predℤ z)
predℤ-ll zero = refl
predℤ-ll (pos x) = refl
predℤ-ll (neg x) = refl

succ-tt : (z : ℤ) → succℤ (tt z) ＝ rr z
succ-tt zero = refl
succ-tt (pos x) = refl
succ-tt (neg x) = refl

pred-tt : (z : ℤ) → predℤ (tt z) ＝ ll z
pred-tt zero = refl
pred-tt (pos x) = refl
pred-tt (neg x) = refl

succℤ-neg-succ𝕋 : (x : 𝕋) → succℤ (neg (succ𝕋 x)) ＝ neg x
succℤ-neg-succ𝕋 one = refl
succℤ-neg-succ𝕋 (L x) = refl
succℤ-neg-succ𝕋 (T x) = refl
succℤ-neg-succ𝕋 (R x) = ap ll (succℤ-neg-succ𝕋 x)

predℤ-pos-succ𝕋 : (x : 𝕋) → predℤ (pos (succ𝕋 x)) ＝ pos x
predℤ-pos-succ𝕋 one = refl
predℤ-pos-succ𝕋 (L x) = refl
predℤ-pos-succ𝕋 (T x) = refl
predℤ-pos-succ𝕋 (R x) = ap rr (predℤ-pos-succ𝕋 x)

ℤ-succ-pred₀ : (x : 𝕋) → succℤ (predℤ (pos x)) ＝ pos x
ℤ-succ-pred₀ one = refl
ℤ-succ-pred₀ (L x) = succℤ-rr (predℤ (pos x)) ∙ ap ll (ℤ-succ-pred₀ x)
ℤ-succ-pred₀ (T x) = refl
ℤ-succ-pred₀ (R x) = refl

ℤ-succ-pred : (z : ℤ) → succℤ (predℤ z) ＝ z
ℤ-succ-pred zero = refl
ℤ-succ-pred (pos x) = ℤ-succ-pred₀ x
ℤ-succ-pred (neg x) = succℤ-neg-succ𝕋 x

ℤ-pred-succ₀ : (x : 𝕋) → predℤ (succℤ (neg x)) ＝ neg x
ℤ-pred-succ₀ one = refl
ℤ-pred-succ₀ (L x) = predℤ-ll (succℤ (neg x)) ∙ ap rr (ℤ-pred-succ₀ x)
ℤ-pred-succ₀ (T x) = refl
ℤ-pred-succ₀ (R x) = refl

ℤ-pred-succ : (z : ℤ) → predℤ (succℤ z) ＝ z
ℤ-pred-succ zero = refl
ℤ-pred-succ (pos x) = predℤ-pos-succ𝕋 x
ℤ-pred-succ (neg x) = ℤ-pred-succ₀ x

ℤ-ternary-induction : (A : ℤ → 𝓤 ̇ )
            → A zero
            → ((k : ℤ) → A k → A (ll k))
            → ((k : ℤ) → A k → A (tt k))
            → ((k : ℤ) → A k → A (rr k))
            → (z : ℤ) → A z
ℤ-ternary-induction A base f g h zero = base
ℤ-ternary-induction A base f g h (pos one) = h zero base
ℤ-ternary-induction A base f g h (pos (L x)) = f (pos x) (ℤ-ternary-induction A base f g h (pos x))
ℤ-ternary-induction A base f g h (pos (T x)) = g (pos x) (ℤ-ternary-induction A base f g h (pos x))
ℤ-ternary-induction A base f g h (pos (R x)) = h (pos x) (ℤ-ternary-induction A base f g h (pos x))
ℤ-ternary-induction A base f g h (neg one) = f zero base
ℤ-ternary-induction A base f g h (neg (L x)) = h (neg x) (ℤ-ternary-induction A base f g h (neg x))
ℤ-ternary-induction A base f g h (neg (T x)) = g (neg x) (ℤ-ternary-induction A base f g h (neg x))
ℤ-ternary-induction A base f g h (neg (R x)) = f (neg x) (ℤ-ternary-induction A base f g h (neg x))

𝕋-natural-induction : (A : 𝕋 → 𝓤 ̇ )
                    → A one
                    → ((k : 𝕋) → A k → A (succ𝕋 k))
                    → (t : 𝕋) → A t
𝕋-natural-induction A base step one = base
𝕋-natural-induction A base step (L t) = 𝕋-natural-induction (λ z → A (L z)) (step one base)
                                         (λ k z → step (R k) (step (T k) (step (L k) z))) t
𝕋-natural-induction A base step (T t) = 𝕋-natural-induction (λ z → A (T z)) (step (L one) (step one base))
                                         (λ k z → step (L (succ𝕋 k)) (step (R k) (step (T k) z))) t
𝕋-natural-induction A base step (R t) = 𝕋-natural-induction (λ z → A (R z))
                                         (step (T one) (step (L one) (step one base)))
                                         (λ k z → step (T (succ𝕋 k)) (step (L (succ𝕋 k)) (step (R k) z))) t

ℤ-induction : (A : ℤ → 𝓤 ̇ )
            → A zero
            → ((k : ℤ) → A k → A (succℤ k))
            → ((k : ℤ) → A k → A (predℤ k))
            → (z : ℤ) → A z
ℤ-induction {𝓤} A base step+ step- zero = base
ℤ-induction {𝓤} A base step+ step- (pos x) =
  𝕋-natural-induction (λ z → A (pos z)) (step+ zero base) (λ k → step+ (pos k)) x
ℤ-induction {𝓤} A base step+ step- (neg x) =
  𝕋-natural-induction (λ z → A (neg z)) (step- zero base) (λ k → step- (neg k)) x

--triple-tt : (z : ℤ) → tripleℤ

_+_ : ℤ → ℤ → ℤ
x + zero = x
x + pos one = succℤ x
x + pos (L y) = predℤ (x + pos y + pos y + pos y)
x + pos (T y) = x + pos y + pos y + pos y
x + pos (R y) = succℤ (x + pos y + pos y + pos y)
x + neg one = predℤ x
x + neg (L y) = succℤ (x + neg y + neg y + neg y) -- x + -(3y-1) = x - 3y + 1
x + neg (T y) = x + neg y + neg y + neg y
x + neg (R y) = predℤ (x + neg y + neg y + neg y) -- x + -(3x+1) = x - 3x - 1

_-_ : ℤ → ℤ → ℤ
x - zero = x
x - pos y = x + neg y
x - neg y = x + pos y

infixl 31 _-_
infixl 31 _+_

addition-ll : (x : ℤ) → predℤ (x + x + x) ＝ ll x
addition-ll x = ℤ-induction (λ z → predℤ (z + z + z) ＝ ll z) refl {!!} {!!} x
  where
    I : (k : ℤ) → predℤ (k + k + k) ＝ ll k → predℤ (succℤ k + succℤ k + succℤ k) ＝ ll (succℤ k)
    I k l = {!!}

addition-tt : (x : ℤ) → x + x + x ＝ tt x
addition-tt zero = refl
addition-tt (pos x) = {!!}
addition-tt (neg x) = {!!}

zero-left-neutral-pos : (x : 𝕋) → zero + pos x ＝ pos x
zero-left-neutral-pos one = refl
zero-left-neutral-pos (L x) = {!!}
zero-left-neutral-pos (T x) = {!!}
zero-left-neutral-pos (R x) = {!!}

zero-left-neutral : (z : ℤ) → zero + z ＝ z
zero-left-neutral zero = refl
zero-left-neutral (pos x) = {!!}
zero-left-neutral (neg x) = {!!}

ℤ-addition-commutative : (a b : ℤ) → a + b ＝ b + a
ℤ-addition-commutative zero b = {!!}
ℤ-addition-commutative (pos x) b = {!!}
ℤ-addition-commutative (neg x) b = {!!}
