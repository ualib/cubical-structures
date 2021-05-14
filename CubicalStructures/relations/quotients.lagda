---
layout: default
title : Relations.Quotients module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="equivalence-relations-and-quotients">Equivalence Relations and Quotients</a>

This section presents the [Relations.Quotients][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --cubical #-}

-- Imports from the Agda (Builtin) and the Agda Standard Library
open import Agda.Primitive using (_⊔_; lsuc)
open import Relation.Unary using (Pred; _∈_; _⊆_)
open import Function.Base using (_on_)

-- Imports from Cubical Agda
open import Cubical.Core.Primitives using (_≡_; Type; Level; _,_; Σ-syntax; Typeω; transp; i0; i1; fst)
open import Cubical.Foundations.Prelude using (refl; sym; _∙_; cong; isProp)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Relation.Binary.Base as CBinary renaming (Rel to REL) using (EquivRel)
open CBinary.BinaryRelation renaming (isEquivRel to IsEquivalence)
open import Cubical.HITs.TypeQuotients using (_/ₜ_; [_]; eq/)

open import Cubical.Data.Sigma using (_×_)

open import overture.preliminaries using (∣_∣; ∥_∥; _⁻¹)
open import relations.discrete renaming (Rel to BinRel) using (ker; PropExt)


module relations.quotients where

variable
 α β 𝓤 𝓥 𝓦 𝓧 𝓨 𝓩 : Level

Refl : {A : Type 𝓤} → BinRel A 𝓦 → Type(𝓤 ⊔ 𝓦)
Refl _≈_ = ∀{x} → x ≈ x

Symm : {A : Type 𝓤} → BinRel A 𝓦 → Type(𝓤 ⊔ 𝓦)
Symm _≈_ = ∀{x}{y} → x ≈ y → y ≈ x

Antisymm : {A : Type 𝓤} → BinRel A 𝓦 → Type(𝓤 ⊔ 𝓦)
Antisymm _≈_ = ∀{x}{y} → x ≈ y → y ≈ x → x ≡ y

Trans : {A : Type 𝓤} → BinRel A 𝓦 → Type(𝓤 ⊔ 𝓦)
Trans _≈_ = ∀{x}{y}{z} → x ≈ y → y ≈ z → x ≈ z

Equivalence : {α β : Level} → Type β → Type (lsuc α ⊔ β)
Equivalence {α}{β} B = Σ[ r ∈ BinRel B α ] IsEquivalence r

open IsEquivalence

module _ {I : Type 𝓥} {A : Type 𝓤 } where

 𝟎 : BinRel (I → A) (𝓥 ⊔ 𝓤)
 𝟎 x y = ∀ i → x i ≡ y i

 𝟎-IsEquivalence : IsEquivalence 𝟎
 𝟎-IsEquivalence = equivRel
                   (λ a i _ → a i)                        -- reflexive
                   (λ a b p i i₁ → sym (p i) i₁)          -- symmetric
                   (λ a b c p q i i₁ → ((p i)∙(q i)) i₁)  -- transitive

 𝟎-IsEquivalence' : IsEquivalence 𝟎
 𝟎-IsEquivalence' = record
                    { reflexive = λ a i → refl
                    ; symmetric = λ a b x i → sym (x i)
                    ; transitive = λ a b c x y i → (x i ∙ y i) }


𝟎-is-smallest : Typeω
𝟎-is-smallest = ∀{𝓥}{𝓤}{𝓦}{I : Type 𝓥}{A : Type 𝓤}(ρ : BinRel (I → A) 𝓦)
 →              IsEquivalence ρ → (x y : I → A) → 𝟎 x y → ρ x y


ker-IsEquivalence : {A : Type 𝓤}{B : Type 𝓦}(f : A → B) → IsEquivalence (ker f)
ker-IsEquivalence f = record
                      { reflexive = λ a i → f a
                      ; symmetric = λ a b → sym
                      ; transitive = λ a b c → _∙_ }


kernel-lemma : {𝓥 𝓤 : Level} → 𝟎-is-smallest
 →             {I : Type 𝓥}{A : Type 𝓤}(f : (I → A) → A)(x y : I → A)
 →             (∀ i → x i ≡ y i) → (ker f) x y

kernel-lemma {𝓥}{𝓤} 0min {I = I}{A = A} f x y hyp =
 0min (ker f) (ker-IsEquivalence{𝓤 = (𝓥 ⊔ 𝓤)}{A = (I → A)} f) x y hyp


{- Old quotient development.

   The next two submodules contain the types we previously used for handling quotients.
   These may still be of some use even after we incorporate the "type quotient" defined
   as a higher inductive type in Cubical Agda as follows:

   ```
   -- Type quotients as a higher inductive type:
   data _/ₜ_ {ℓ ℓ'} (A : Type ℓ) (R : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
   [_] : (a : A) → A /ₜ R
   eq/ : (a b : A) → (r : R a b) → [ a ] ≡ [ b ]
   ```
-}


{- Blocks of partitions.
   Before defining the quotient type, we define a type representing inhabitants of quotients;
   i.e., blocks of a partition (recall partitions correspond to equivalence relations) -}

[_/_]ₙ : {B : Type β} → B → Equivalence{α} B → Pred B α
[ u / R ]ₙ = ∣ R ∣ u


isProp[_/_] : {B : Type β} → B → Equivalence{α} B → Type (α ⊔ β)
isProp[ u / R ] = (∀ x → isProp (x ∈ [ u / R ]ₙ))


-- infix 60 [_/_]ₙ

module _ {B : Type β}{R : Equivalence{α} B} where

 []-⊆ : {u v : B} → ∣ R ∣ u v →  [ u / R ]ₙ ⊆ [ v / R ]ₙ
 []-⊆ {u}{v} Ruv {x} ux = transitive ∥ R ∥ v u x (symmetric ∥ R ∥ u v Ruv) ux

 []-⊇ : {u v : B} → ∣ R ∣ u v → [ v / R ]ₙ ⊆ [ u / R ]ₙ
 []-⊇ {u}{v} Ruv {x} Rvx = transitive ∥ R ∥ u v x Ruv Rvx

 {- If we assume that for each x there is at most one proof that x ∈ [ u / R ],
    and similarly for x ∈ [ v / R ], then we can prove the following equivalence
    of blocks of an equivalence relation. -}
 []≡-intro : (u v : B) → isProp[ u / R ] → isProp[ v / R ]
  →          ∣ R ∣ u v → [ u / R ]ₙ ≡ [ v / R ]ₙ

 []≡-intro u v propu propv uv = PropExt ([ u / R ]ₙ) ([ v / R ]ₙ) propu propv ([]-⊆ uv) ([]-⊇ uv)

 []≡-elim : {u v : B} → [ u / R ]ₙ ≡ [ v / R ]ₙ → ∣ R ∣ u v
 []≡-elim {u}{v} uv = goal
  where
  ξ : v ∈ [ v / R ]ₙ
  ξ = reflexive ∥ R ∥ v
  goal : v ∈ [ u / R ]ₙ
  goal = transp (λ i → (uv ⁻¹) i v ) i0 ξ


 IsBlock : (C : Pred B _) → Type (lsuc α ⊔ β)
 IsBlock C = Σ[ u ∈ B ] C ≡ [ u / R ]ₙ


-- Quotients.
_/_ : (B : Type β ) → Equivalence{α} B → Type (lsuc α ⊔ β)
B / R = Σ[ C ∈ Pred B _ ] IsBlock {R = R} C

infix -1 _/_
module _ {B : Type β} where

 ⟪_/_⟫ : B → (R : Equivalence {α} B) → B / R
 ⟪ b / R ⟫ = [ b / R ]ₙ , (b  , refl)

 _⌞_⌟ : (R : Equivalence {α} B) → B / R  → B
 R ⌞ C , b , p ⌟ = b

module _ {B : Type β}{R : Equivalence {α} B} where

 ⟪⟫≡-elim : {u v : B} → ⟪ u / R ⟫ ≡ ⟪ v / R ⟫ → ∣ R ∣ u v
 ⟪⟫≡-elim uv = []≡-elim {R = R}(cong fst uv)

\end{code}

-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------






















<!-- NO LONGER NEEDED ------------------------------------------------------------


open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (_⊔_; lzero; lsuc; Level; Setω)
open import Data.Product  using (_,_; Σ; Σ-syntax; _×_)
open import Relation.Binary using (Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Relation.Unary using (Pred; _⊆_)

---------------------------------------------------------------------------- -->
