---
layout: default
title : structures.congruences module (cubical-structures library)
date : 2021-05-12
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --cubical #-}

open import Agda.Primitive using (_⊔_; lsuc)
open import Relation.Unary using (Pred; _∈_)

open import Cubical.Core.Primitives using (_≡_; Type; Level; Σ-syntax;  i0; i1; fst; snd; _,_)
open import Cubical.Data.Sigma.Base using (_×_)
open import Cubical.Foundations.Prelude using (refl; sym; _∙_; funExt; cong; _∎; _≡⟨_⟩_; Lift; lift)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Relation.Binary.Base as CBinary renaming (Rel to REL) using (EquivRel)
open CBinary.BinaryRelation renaming (isEquivRel to IsEquivalence)

-- Imports from the Agda Universal Algebra Library
open import overture.preliminaries using (𝓘; 𝓞; 𝓤; 𝓥; 𝓦; 𝓧; 𝓨; 𝓩; Π; -Π; _⁻¹; id; ∣_∣)
open import structures.basic
open import overture.inverses using (IsInjective; IsSurjective)
open import relations.discrete renaming (Rel to BinRel) using (_|:_; ker)
open import relations.quotients using (_/_; ⟪_/_⟫; _⌞_⌟; [_/_])
-- open import structures.products



module structures.congruences {𝑅 𝐹 : Signature} where

-- record IsCongruence {α β : Level} (𝑩 : Structure 𝑅 𝐹 {β})(θ : EquivRel ∣ 𝑩 ∣ α) : Type (α ⊔ β)  where
--  constructor mkcon
--  field       is-equivalence : IsEquivalence θ
--              is-compatible  : compatible 𝑩 θ

-- open IsCongruence

Con : {α β : Level}(𝑩 : Structure 𝑅 𝐹 {β}) → Type (lsuc α ⊔ β)
Con {α} 𝑩 = Σ[ θ ∈ EquivRel ∣ 𝑩 ∣ α ] (compatible 𝑩 ∣ θ ∣) -- IsCongruence 𝑩 θ

\end{code}

Each of these types captures what it means to be a congruence and they are equivalent in the sense that each implies the other. One implication is the "uncurry" operation and the other is the second projection.

\begin{code}

-- IsCongruence→Con : {α β : Level}{𝑩 : Structure 𝑅 𝐹 {β}}
--                    (θ : BinRel ∣ 𝑩 ∣ α) → IsCongruence 𝑩 θ → Con{α} 𝑩
-- IsCongruence→Con θ p = θ , p

-- Con→IsCongruence : {α β : Level}{𝑩 : Structure 𝑅 𝐹 {β}}
--                    ((θ , _) : Con{α} 𝑩) → IsCongruence{α} 𝑩 θ
-- Con→IsCongruence θ = snd θ

-- open IsEquivalence


𝟎 : {β : Level}{B : Type β} → BinRel B β
𝟎 x y = x ≡ y
-- Rel : ∀{ℓ} → Type ℓ → (ℓ' : Level) → Type (ℓ ⊔ lsuc ℓ')
-- Rel A ℓ' = REL A A ℓ'

𝟎-IsEquivalence : {β : Level}{B : Type β} →  IsEquivalence {A = B} 𝟎
𝟎-IsEquivalence = record { reflexive = λ a _ → a
                         ; symmetric = λ _ _ x i → sym x i
                         ; transitive = λ _ _ _ 0ab 0bc i → (0ab ∙ 0bc) i
                         }


module _ {α β : Level} {𝑩 : Structure 𝑅 𝐹 {β}} where


 𝟎-compatible-op : (𝑓 : ∣ 𝐹 ∣) → (𝑓 ᵒ 𝑩) |: 𝟎
 𝟎-compatible-op 𝑓 {i}{j} ptws0  = cong (𝑓 ᵒ 𝑩) (funExt ptws0)

 𝟎-compatible :  compatible 𝑩 𝟎
 𝟎-compatible = λ 𝑓 x → 𝟎-compatible-op 𝑓 x

 -- Δ : IsCongruence{β}{β} 𝑩 𝟎
 -- Δ = mkcon 𝟎-IsEquivalence 𝟎-compatible

 𝟘 : Con{β} 𝑩
 𝟘 = (𝟎 , 𝟎-IsEquivalence) , 𝟎-compatible --   IsCongruence→Con 𝟎 Δ

\end{code}


A concrete example is `⟪𝟎⟫[ 𝑨 ╱ θ ]`, presented in the next subsection.

#### <a id="quotient-algebras">Quotient algebras</a>

\begin{code}

module _ {α β : Level} where

 _╱_ : (𝑩 : Structure 𝑅 𝐹 {β}) → Con{α} 𝑩 → Structure 𝑅 𝐹

 𝑩 ╱ θ = (∣ 𝑩 ∣ / ∣ θ ∣)                                    -- domain of the quotient algebra
         , (λ 𝑟 x → Lift{β}{lsuc α}((𝑟 ʳ 𝑩) λ i → ∣ θ ∣ ⌞ x i ⌟ )) -- basic relations of the quotient structure
         , λ 𝑓 𝑎 → ⟪ (𝑓 ᵒ 𝑩)(λ i →  ∣ snd (𝑎 i) ∣) / ∣ θ ∣ ⟫          -- basic operations of the quotient algebra

\end{code}

**Example**. If we adopt the notation `𝟎[ 𝑨 ╱ θ ]` for the zero (or identity) relation on the quotient algebra `𝑨 ╱ θ`, then we define the zero relation as follows.

\begin{code}

 𝟘[_╱_] : (𝑩 : Structure 𝑅 𝐹 {β})(θ : Con{α} 𝑩) → BinRel (∣ 𝑩 ∣ / ∣ θ ∣) (lsuc α ⊔ β)
 𝟘[ 𝑩 ╱ θ ] = λ u v → u ≡ v

\end{code}

From this we easily obtain the zero congruence of `𝑨 ╱ θ` by applying the `Δ` function defined above.
\begin{code}

 𝟎[_╱_] : (𝑩 : Structure 𝑅 𝐹 {β})(θ : Con{α} 𝑩) → Con{lsuc α ⊔ β} (𝑩 ╱ θ)
 𝟎[ 𝑩 ╱ θ ] =  𝟘 {α}{lsuc α ⊔ β}{𝑩 ╱ θ}

\end{code}


Finally, the following elimination rule is sometimes

\begin{code}

 -- open IsCongruence

 /-≡ : {𝑩 : Structure 𝑅 𝐹 {β}}( (θ , _ ) : Con{α} 𝑩){u v : ∣ 𝑩 ∣} → ⟪ u / θ ⟫ ≡ ⟪ v / θ ⟫ → ∣ θ ∣ u v
 /-≡ θ {u}{v} x =  {!!} 
--   where
--   goal' : v ∈ [ u ]{∣ θ ∣}
--   goal' = {!!}
--   goal'' : [ u ]{∣ θ ∣} ≡ [ v ]{∣ θ ∣}
--   goal'' = cong fst x
-- --   goal'' = ⟪ a ⟫{R} = [ a ]{R} , (a  , refl)

--   goal : ∣ θ ∣ u v
--   goal = {!!}


  -- λ x → cong fst {!!} {!!}  -- {u}{v} uv =  fst uv -- refl -- (is-equivalence {!snd θ!}) {!!}  -- {!fst!} uv {!!}

-- {!!} {!!} {!!} -- refl = reflexive (is-equivalence {!snd θ!}) {!!} -- IsEquivalence.refl (is-equivalence ∥ θ ∥)

\end{code}

--------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> **Unicode Hints**. Produce the `╱` symbol in [agda2-mode][] by typing `\---` and then `C-f` a number of times.</span>


<br>
<br>

[← Algebras.Products](Algebras.Products.html)
<span style="float:right;">[Homomorphisms →](Homomorphisms.html)</span>

{% include UALib.Links.md %}
























<!-- NO LONGER NEEDED ----------------------------------------------------------

-- Imports from the Agda (Builtin) and the Agda Standard Library
-- open import Agda.Builtin.Equality using (_≡_; refl)
-- open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
-- open import Level renaming (suc to lsuc; zero to lzero)
-- open import Data.Product using (_,_; Σ; _×_)
-- open import Relation.Binary using (Rel; IsEquivalence)
-- open import Relation.Unary using (Pred; _∈_)
-- open import Relation.Binary.PropositionalEquality.Core using (sym; trans; cong)

-- -- Imports from the Agda Universal Algebra Library
-- open import Algebras.Basic
-- open import Overture.Preliminaries using (Type; 𝓘; 𝓞; 𝓤; 𝓥; 𝓦; Π; -Π; -Σ; ∣_∣; ∥_∥; fst)
-- open import Relations.Discrete using (𝟎; _|:_)
-- open import Relations.Quotients using (_/_; ⟪_⟫)

--------------------------------------------------------------------------------- -->
