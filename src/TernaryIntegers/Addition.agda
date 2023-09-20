{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

open import UF.FunExt

module TernaryIntegers.Addition where

open import MLTT.Spartan renaming (_+_ to _⊹_)
open import TernaryIntegers.Type public
open import TernaryIntegers.Negation public

_+₀_ : ℤ₀ → ℤ₀ → ℤ
x +₀ one = succℤ₀ x
x +₀ negone = predℤ₀ x
one +₀ L y = η (T y)
negone +₀ L y = predℤ₀ (L y)
L x +₀ L y = predℤ (ll (x +₀ y))
T x +₀ L y = ll (x +₀ y)
R x +₀ L y = tt (x +₀ y)
one +₀ T y = η (R y)
negone +₀ T y = η (L y)
L x +₀ T y = ll (x +₀ y)
T x +₀ T y = tt (x +₀ y)
R x +₀ T y = rr (x +₀ y)
one +₀ R y = succℤ₀ (R y)
negone +₀ R y = η (T y)
L x +₀ R y = tt (x +₀ y)
T x +₀ R y = rr (x +₀ y)
R x +₀ R y = succℤ (rr (x +₀ y))

_+_ : ℤ → ℤ → ℤ
zero + y = y
η x + zero = η x
η x + η y = x +₀ y

_-_ : ℤ → ℤ → ℤ
x - y = x + (- y)

infixl 31 _-_
infixl 31 _+_
infixl 31 _+₀_


one-plus-is-succ₀ : (x : ℤ₀) → one +₀ x ＝ succℤ₀ x
one-plus-is-succ₀ one = refl
one-plus-is-succ₀ negone = refl
one-plus-is-succ₀ (L x) = refl
one-plus-is-succ₀ (T x) = refl
one-plus-is-succ₀ (R x) = refl

negone-plus-is-pred₀ : (x : ℤ₀) → negone +₀ x ＝ predℤ₀ x
negone-plus-is-pred₀ one = refl
negone-plus-is-pred₀ negone = refl
negone-plus-is-pred₀ (L x) = refl
negone-plus-is-pred₀ (T x) = refl
negone-plus-is-pred₀ (R x) = refl

zero-right-id : (x : ℤ) → x + zero ＝ x
zero-right-id zero = refl
zero-right-id (η x) = refl

-- Addition commutativity
ℤ₀+-commutative : (x y : ℤ₀) → x +₀ y ＝ y +₀ x
ℤ₀+-commutative-l : (x y : ℤ₀) → L x +₀ y ＝ y +₀ L x
ℤ₀+-commutative-t : (x y : ℤ₀) → T x +₀ y ＝ y +₀ T x
ℤ₀+-commutative-r : (x y : ℤ₀) → R x +₀ y ＝ y +₀ R x

ℤ₀+-commutative-l x one = refl
ℤ₀+-commutative-l x negone = refl
ℤ₀+-commutative-l x (L y) = ap (predℤ ∘ ll) (ℤ₀+-commutative x y)
ℤ₀+-commutative-l x (T y) = ap ll (ℤ₀+-commutative x y)
ℤ₀+-commutative-l x (R y) = ap tt (ℤ₀+-commutative x y)

ℤ₀+-commutative-t x one = refl
ℤ₀+-commutative-t x negone = refl
ℤ₀+-commutative-t x (L y) = ap ll (ℤ₀+-commutative x y)
ℤ₀+-commutative-t x (T y) = ap tt (ℤ₀+-commutative x y)
ℤ₀+-commutative-t x (R y) = ap rr (ℤ₀+-commutative x y)

ℤ₀+-commutative-r x one = refl
ℤ₀+-commutative-r x negone = refl
ℤ₀+-commutative-r x (L y) = ap tt (ℤ₀+-commutative x y)
ℤ₀+-commutative-r x (T y) = ap rr (ℤ₀+-commutative x y)
ℤ₀+-commutative-r x (R y) = ap (succℤ ∘ rr) (ℤ₀+-commutative x y)

ℤ₀+-commutative one y = one-plus-is-succ₀ y
ℤ₀+-commutative negone y = negone-plus-is-pred₀ y
ℤ₀+-commutative (L x) y = ℤ₀+-commutative-l x y
ℤ₀+-commutative (T x) y = ℤ₀+-commutative-t x y
ℤ₀+-commutative (R x) y = ℤ₀+-commutative-r x y

ℤ+-commutative : (x y : ℤ) → x + y ＝ y + x
ℤ+-commutative x zero = zero-right-id x
ℤ+-commutative zero (η y) = refl
ℤ+-commutative (η x) (η y) = ℤ₀+-commutative x y
