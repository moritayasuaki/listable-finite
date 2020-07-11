-- Agda version 2.6.0.1
open import Data.Product
open import Data.List
open import Data.Nat
open import Data.Fin
open import Data.Fin.Properties
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

Injection : (A B : Set) -> (A -> B) -> Set
Injection A B f = (x y : A) -> f x ≡ f y -> x ≡ y

LeftInverse : (A B : Set) -> (B -> A) -> (A -> B) -> Set
LeftInverse A B f g = (x : A) -> f ( g x ) ≡ x

Deq : (D : Set) -> Set
Deq D = (x y : D) -> Dec (x ≡ y)

linvAB-injAB : (A B : Set) -> (f : B -> A) -> (g : A -> B) -> LeftInverse A B f g -> Injection A B g
linvAB-injAB A B f g linv-f-g x y gx≡gy with cong f gx≡gy
... | fgx≡fgy rewrite (linv-f-g x) | (linv-f-g y) = fgx≡fgy

injAB-deqB-deqA : (A B : Set) -> (i : A -> B) -> Injection A B i -> Deq B -> Deq A
injAB-deqB-deqA A B i inj-i deqB x y with deqB (i x) (i y)
... | yes ix≡iy = yes (inj-i x y ix≡iy)
... | no ix≢iy = no \x≡y -> ix≢iy (cong i x≡y)

deqFin : {n : ℕ} -> Deq (Fin n)
deqFin zero zero = yes refl
deqFin zero (suc y) = no \()
deqFin (suc x) zero = no \()
deqFin (suc x) (suc y) with deqFin x y
... | yes x≡y = yes (cong suc x≡y)
... | no x≢y = no \sx≡sy -> x≢y (suc-injective sx≡sy)

record Listable (X : Set) : Set where
  field
    xs : List X  -- list includes all value in X
    ∀x∈xs : ∀ x -> x ∈ xs -- proof of membership which has a form like `there ( there .. (there here) .. )` for each x in X

  private
    locate' : (x : X) -> (yys : List X) -> (x ∈ yys) -> Fin (length yys)
    locate' x (y ∷ ys) (here x≡y) = Fin.zero
    locate' x (y ∷ ys) (there x∈ys) = Fin.suc (locate' x ys x∈ys)

    -- lookup-locate' checks the predicate `lookup yys (locate' x yys x∈yys) ≡ x` holds recursively
    lookup-locate' : (x : X) -> (yys : List X) -> (x∈yys : x ∈ yys) -> (n : Fin (length yys)) ->
                  (locate' x yys x∈yys ≡ n) -> (lookup yys n ≡ x)
    lookup-locate' x (y ∷ ys) (here x≡y) Fin.zero loc-x-yys-x∈yys≡z rewrite x≡y = refl
    lookup-locate' x (y ∷ ys) (there x∈ys) (Fin.suc n) loc-x-yys-x∈yys≡sn = lookup-locate' x ys x∈ys n (suc-injective loc-x-yys-x∈yys≡sn)

  -- we will get injection to natural number less than `length xs` which can be considered as index of xs
  I : Set
  I = Fin (length xs)

  -- `locate` maps element x (and its proof of membership) into index
  locate : X -> I
  locate x = locate' x xs (∀x∈xs x)

  -- `lookup'` just takes i-th element of xs
  lookup' : I -> X
  lookup' i = lookup xs i

  linv : LeftInverse X I lookup' locate
  linv x = lookup-locate' x xs (∀x∈xs x) (locate x) refl

  inj : Injection X I locate
  inj = linvAB-injAB X I lookup' locate linv

  deq : Deq X
  deq = injAB-deqB-deqA X I locate inj deqFin
