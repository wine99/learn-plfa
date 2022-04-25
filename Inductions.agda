import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p
  rewrite +-assoc m n p = refl

+-identityʳ : ∀ (n : ℕ) → n + zero ≡ n
+-identityʳ zero = refl
+-identityʳ (suc n)
  rewrite +-identityʳ n = refl

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n
  rewrite +-suc m n = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero
  rewrite +-identityʳ m = refl
+-comm m (suc n)
  rewrite +-suc m n | +-comm m n = refl


+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p
  rewrite sym (+-assoc m n p)
        | +-comm m n
        | +-assoc n m p
        = refl


*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p
  rewrite *-distrib-+ m n p
        | +-assoc p (m * p) (n * p) = refl


*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p
  rewrite *-distrib-+ n (m * n) p
        | *-assoc m n p = refl


*-nilʳ : ∀ m → m * 0 ≡ 0
*-nilʳ zero = refl
*-nilʳ (suc m)
  rewrite *-nilʳ m = refl

*-suc : ∀ (m n : ℕ) → n * suc m ≡ n + n * m
*-suc m zero = refl
*-suc m (suc n)
  rewrite *-suc m n
        | sym (+-assoc m n (n * m))
        | +-comm m n
        | +-assoc n m (n * m)
        = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n
  rewrite *-nilʳ n = refl
*-comm (suc m) n
  rewrite *-comm m n
        | *-suc m n
        = refl


0∸n≡0 : ∀ (n : ℕ) → 0 ∸ n ≡ 0
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl


∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero n p
  rewrite 0∸n≡0 n
        | 0∸n≡0 p
        | 0∸n≡0 (n + p)
        = refl
∸-+-assoc (suc m) zero p = refl
∸-+-assoc (suc m) (suc n) p
  rewrite ∸-+-assoc m n p = refl


^-distribˡ-+-* : ∀ (m n p : ℕ) →  m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m zero p
  rewrite +-identityʳ (m ^ p) = refl
^-distribˡ-+-* m (suc n) p
  rewrite ^-distribˡ-+-* m n p
        | *-assoc m (m ^ n) (m ^ p) = refl


^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p)
  rewrite ^-distribʳ-* m n p
        | *-assoc m n (m ^ p * n ^ p)
        | sym (*-assoc n (m ^ p) (n ^ p))
        | *-comm n (m ^ p)
        | *-assoc (m ^ p) n (n ^ p)
        | sym (*-assoc m (m ^ p) (n * (n ^ p)))
        = refl


^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero
  rewrite *-nilʳ n = refl
^-*-assoc m n (suc p)
  rewrite *-suc p n
        | ^-distribˡ-+-* m n (n * p)
        | ^-*-assoc m n p
        = refl


data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = zero
from (b O) = 0 + 2 * from b
from (b I) = 1 + 2 * from b


inc-suc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
inc-suc ⟨⟩ = refl
inc-suc (b O) = refl
inc-suc (b I)
  rewrite +-identityʳ (from (inc b))
        | +-identityʳ (from b)
        | inc-suc b
        | +-suc (from b) (from b)
        = refl


to-from-counter-eg : to (from ⟨⟩) ≡ ⟨⟩ O
to-from-counter-eg = refl


from-to : ∀ (n : ℕ) → from (to n) ≡ n
from-to zero = refl
from-to (suc n)
  rewrite inc-suc (to n)
        | from-to n
        = refl

