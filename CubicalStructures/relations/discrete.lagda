---
layout: default
title : relations.discrete module
date : 2021-05-08
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --cubical #-}


-- Imports from the Agda (Builtin) and the Agda Standard Library
open import Agda.Primitive using (_⊔_; lsuc)
open import Relation.Unary using (Pred; _∈_; _⊆_)
open import Function.Base using (_on_)

-- Imports from Cubical Agda
open import Cubical.Core.Primitives using (_≡_; Type; Level; _,_; Σ-syntax; transp; i0; i1)
open import Cubical.Foundations.Prelude using (refl; sym; _∙_; cong; transport; funExt; isProp)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Relation.Binary.Base renaming (Rel to REL) using ()
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Foundations.Univalence using (hPropExt)


module relations.discrete where

variable
 α β γ δ 𝓥 : Level

{-Unary relations. The unary relation (or "predicate") type is imported from
  Relation.Unary of the std lib.
  ```
  Pred : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
  Pred A ℓ = A → Set ℓ
  ```
-}

module _ {α β : Level}{B : Type β}
         (P Q : Pred B α) where

 -- Naturally, if P ≡ Q, then P ⊆ Q and Q ⊆ P.
 ≡→⊆ : P ≡ Q → P ⊆ Q
 ≡→⊆ pq {x} Px = transp (λ i → pq i x) i0 Px

 -- In cubical tt, we can also prove the converse!
 PropExt : (∀ x → isProp (P x)) → (∀ x → isProp (Q x)) → P ⊆ Q → Q ⊆ P → P ≡ Q
 PropExt Pprop Qprop φ ψ = funExt goal
  where
  goal : (x : B) → P x ≡ Q x
  goal x = hPropExt (Pprop x) (Qprop x) φ ψ


{-Binary relations. The binary relation type `Rel` in Cubical.Relation.Binary.Base
  is the more general (heterogeneous) binary relation so we rename it `REL` and
  use Rel for the homomgeneous binary relation (like in the standard library).
  (This just saves us from having to repeat the domain type of homogeneous relations.)

  The heterogeneous binary relation type is imported from Cubical.Relation.Binary.Base.
  ```
  REL : ∀ {ℓ} (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
  REL A B ℓ' = A → B → Type ℓ'
  ```-}
-- Homogeneous binary relation type
Rel : ∀{ℓ} → Type ℓ → (ℓ' : Level) → Type (ℓ ⊔ lsuc ℓ')
Rel A ℓ' = REL A A ℓ'

module _ {A : Type α}{B : Type β} where

 ker : (A → B) → Rel A β
 ker g x y = g x ≡ g y

 ker' : (A → B) → (I : Type 𝓥) → Rel (I → A) (β ⊔ 𝓥)
 ker' g I x y = g ∘ x ≡ g ∘ y

 kernel : (A → B) → Pred (A × A) β
 kernel g (x , y) = g x ≡ g y


module _ {A : Type α } where

 𝟎 : Rel A α
 𝟎 x y = x ≡ y

 𝟎-pred : Pred (A × A) α
 𝟎-pred (x , y) = x ≡ y

 𝟎-sigma : Type α
 𝟎-sigma = Σ[ x ∈ A ] Σ[ y ∈ A ] x ≡ y

 𝟎-sigma' : Type α
 𝟎-sigma' = Σ[ (x , y) ∈ A × A ] x ≡ y

-- The following type denotes the assertion that the image of a given
-- function is contained in a given subset of the codomain.
Im_⊆_ : {A : Type α}{B : Type β} → (A → B) → Pred B γ → Type (α ⊔ γ)
Im f ⊆ S = ∀ x → f x ∈ S



-- Operations.
-- The following type denotes operations of arity I on type A.
Op : Type 𝓥 → Type α → Type(α ⊔ 𝓥)
Op I A = (I → A) → A

-- Example (projections)
π : {I : Type 𝓥 } {A : Type α } → I → Op I A
π i x = x i



{-Compatibility of binary relations. We now define the function `compatible` so
  that, if `𝑩` denotes a structure and `r` a binary relation, then `compatible 𝑩
  r` will represent the assertion that `r` is *compatible* with all basic
  operations of `𝑩`. in the following sense:
  `∀ 𝑓 : ∣ 𝐹 ∣ → ∀(x y : ∥ 𝐹 ∥ 𝑓 → ∣ 𝑩 ∣) → (∀ i → r (x i)(y i)) → r (f x)(f y)` -}
eval-rel : {A : Type α}{I : Type 𝓥} → Rel A β → Rel (I → A)(𝓥 ⊔ β)
eval-rel R u v = ∀ i → R (u i) (v i)

compatible-op : {A : Type α}{I : Type 𝓥} → Op I A → Rel A β → Type(α ⊔ 𝓥 ⊔ β)
compatible-op f R  = ∀ u v → (eval-rel R) u v → R (f u) (f v)


{-Fancy notation for compatible-op. We omit the previously used import of
  `Relation.Binary.Core using (REL; Rel; _⇒_;_=[_]⇒_)` since we will redefine
  _⇒_ and _=[_]⇒_ to be sure they're compatible with Cubical Agda.
  Note to self: have a look at module Cubical.Functions.Logic when you get a
  chance. Maybe there's something there we can use instead.

  NOTE: `_⇒_` and `_=[_]⇒_` are lifted from `Relation.Binary.Core`
  (modulo minor syntax mods) -}
variable
 A : Type α
 B : Type β

infix 4 _⇒_ _=[_]⇒_
_⇒_ : REL A B γ → REL A B δ → Type _
P ⇒ Q = ∀ {x y} → P x y → Q x y

-- Generalised implication - if P ≡ Q it can be read as "f preserves P".
_=[_]⇒_ : Rel A γ → (A → B) → Rel B δ → Type _
P =[ f ]⇒ Q = P ⇒ (Q on f)

_|:_ : {I : Type 𝓥} → Op I A → Rel A β → Type _
f |: R  = (eval-rel R) =[ f ]⇒ R

\end{code}


-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------

















<!-- No longer needed -------------------------------

-- open import Agda.Builtin.Equality using (_≡_)
-- open import Agda.Primitive using (_⊔_; lzero; lsuc; Level)
-- open import Data.Empty using (⊥)
-- open import Data.Product using (_,_; Σ; Σ-syntax; _×_)
-- open import Data.Sum.Base using (_⊎_)
-- open import Function.Base  using (_∘_)
-- open import Relation.Unary using (∅; Pred; _∪_; _∈_; _⊆_; ｛_｝)
-- open import Agda.Builtin.Bool using (true; false)
-- open import Relation.Nullary using (Dec; _because_; ofʸ)


-- open import Data.Product using (∃; ∃-syntax)


-- A synonym for _=[_]⇒_.

_Preserves_⟶_ : (A → B) → Rel A ℓ₁ → Rel B ℓ₂ → Set _
f Preserves P ⟶ Q = P =[ f ]⇒ Q

-- A binary variant of _Preserves_⟶_.
_Preserves₂_⟶_⟶_ : (A → B → C) → Rel A ℓ₁ → Rel B ℓ₂ → Rel C ℓ₃ → Set _
_∙_ Preserves₂ P ⟶ Q ⟶ R = ∀ {x y u v} → P x y → Q u v → R (x ∙ u) (y ∙ v)



--------------------------------------------------------------------- -->
