{-# OPTIONS --rewriting #-}

data FALSE : Set where

CONTRADICTION : ∀ {A : Set} → FALSE → A
CONTRADICTION ()

record TRUE : Set where
{-# BUILTIN UNIT TRUE #-}

data Bool : Set where
  false true : Bool
{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

data Nat : Set where
  zero : Nat
  suc : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

_+_ : Nat → Nat → Nat
zero  + m = m
suc n + m = suc (n + m)
{-# BUILTIN NATPLUS _+_ #-}

_-_ : Nat → Nat → Nat
n     - zero  = n
zero  - suc m = zero
suc n - suc m = n - m
{-# BUILTIN NATMINUS _-_ #-}

_*_ : Nat → Nat → Nat
zero  * m = zero
suc n * m = (n * m) + m
{-# BUILTIN NATTIMES _*_ #-}

_==_ : Nat → Nat → Bool
zero  == zero  = true
suc n == suc m = n == m
_     == _     = false
{-# BUILTIN NATEQUALS _==_ #-}

postulate String : Set
{-# BUILTIN STRING String #-}

primitive
  primStringAppend   : String → String → String
  primStringEquality : String → String → Bool

_+++_ = primStringAppend
_===_ = primStringEquality

data List(A : Set) : Set where
  nil : List(A)
  _::_ : A → List(A) → List(A)
{-# BUILTIN LIST List  #-}

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x
{-# BUILTIN EQUALITY _≡_  #-}
{-# BUILTIN REWRITE _≡_ #-}

cong : ∀ {a} {X Y : Set a} {x y : X} (f : X → Y) → (x ≡ y) → (f x ≡ f y)
cong f refl = refl

_≢_ :  ∀ {a} {A : Set a} → A → A → Set a
(x ≢ y) = (x ≡ y) → FALSE

data Dec(A : Set) : Set where
  yes : A → Dec(A)
  no : (A → FALSE) → Dec(A)

primitive
  primEraseEquality : ∀ {a} {A : Set a} {x y : A} → x ≡ y → x ≡ y

primTrustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y
primTrustMe {x = x} {y} = primEraseEquality unsafePrimTrustMe where
   postulate unsafePrimTrustMe : x ≡ y

_≟String_ : (s t : String) → Dec(s ≡ t)
(s ≟String t) with primStringEquality s t
(s ≟String t) | true = yes primTrustMe
(s ≟String t) | false = no unsafeNo where
  postulate unsafeNo : s ≢ t

_≟Nat_ : (m n : Nat) → Dec(m ≡ n)
(m ≟Nat n) with m == n
(m ≟Nat n) | true = yes primTrustMe
(m ≟Nat n) | false = no unsafeNo where
  postulate unsafeNo : m ≢ n

data _≤_ : Nat → Nat → Set where
  zero : ∀ {x} → zero ≤ x
  suc : ∀ {x y} → (x ≤ y) → (suc x ≤ suc y)

_≤?_ : (x y : Nat) → Dec(x ≤ y)
zero ≤? y = yes zero
suc x ≤? zero = no (λ ())
suc x ≤? suc y with (x ≤? y)
... | yes p = yes (suc p)
... | no  p = no  (λ { (suc q) → p q })

_<_ : Nat → Nat → Set
m < n = (n ≤ m) → FALSE

asym : ∀ {m n} → (m ≤ n) → (n ≤ m) → (m ≡ n)
asym zero zero = refl
asym (suc p) (suc q) with asym p q
asym (suc p) (suc q) | refl = refl

if : ∀ {X Y : Set} → Dec(X) → Y → Y → Y
if (yes p) x y = x
if (no  p) x y = y

+zero : ∀ {m} → (m + zero) ≡ m
+zero {zero} = refl
+zero {suc m} = cong suc +zero

+suc : ∀ {m n} → (m + suc n) ≡ suc (m + n)
+suc {zero} = refl
+suc {suc m} = cong suc +suc

{-# REWRITE +zero +suc #-}
