/* 
---------------------------------------------------------------------------
Library on rewrite-tactic-based clausification of Leo-III
---------------------------------------------------------------------------

This file contains boolean equalities that complement the theorems
already present in the Lambdapi standard library with additional
boolean identities necessary for the full verification of the Leo-III
clausification procedure.
---------------------------------------------------------------------------
*/

require open Stdlib.FunExt Stdlib.PropExt Stdlib.Epsilon;

/******************************************************************************
*  Handling of Connectives        
******************************************************************************/

opaque symbol ∨_sym x y : π ((x ∨ y) = (y ∨ x))≔
begin
  assume x y;
  refine propExt (x ∨ y) (y ∨ x) _ _
    {assume h0;
    refine ∨ₑ h0 _ _
      {assume h1; refine ∨ᵢ₂ h1}
      {assume h1; refine ∨ᵢ₁ h1}}
    {assume h0;
    refine ∨ₑ h0 _ _
      {assume h1; refine ∨ᵢ₂ h1}
      {assume h1; refine ∨ᵢ₁ h1}}
end;

opaque symbol ∧_sym x y : π ((x ∧ y) = (y ∧ x))≔
begin
  assume x y;
  refine propExt (x ∧ y) (y ∧ x) _ _
    {assume h; refine ∧ᵢ (∧ₑ₂ h) (∧ₑ₁ h)}
    {assume h; refine ∧ᵢ (∧ₑ₂ h) (∧ₑ₁ h)}
end;

opaque symbol ¬x=_idem : Π x, 
    π (((¬ x) = x) = ⊥)≔
begin
    assume x;
    refine propExt ((¬ x )= x) ⊥ _ _
        {assume h; 
        refine ∨ₑ [x] [¬ x] [⊥] (em x) _ _
            {assume h0;
            refine =⇒ (eq_sym h) h0 h0}
            {assume h0;
            refine h0 (=⇒ h h0)}}
        {assume h;
        refine ⊥ₑ h}
end;

opaque symbol =¬x_idem : Π x, 
    π ((x = (¬ x)) = ⊥)≔
begin
    assume x;
    rewrite =_sym x (¬ x);
    refine ¬x=_idem x
end;

opaque symbol =⊥' x : π (¬ (x = ⊥) = x)≔
begin
	assume x;
	rewrite =⊥;
	rewrite ¬¬ₑ_eq;
	reflexivity
end;

opaque symbol ⊥=' x : π (¬ (⊥ = x) = x)≔
begin
	assume x;
	rewrite ⊥=;
	rewrite ¬¬ₑ_eq;
	reflexivity
end;

/******************************************************************************
*  Binder Handling   
******************************************************************************/

opaque symbol eta_exp [a] [b] (f : τ a → τ b) :  
    π (f = (λ y , f y))≔
begin
    assume a b f; 
    refine funExt f (λ y , f y) _;
    simplify; reflexivity
end;

opaque symbol eta_exp_∀ [a : Set] (f : τ (a ⤳ o)) : 
    π(∀ f = `∀ x, f x)≔
begin
    assume a f;
    rewrite .[x in ∀ x = _] eta_exp f;
    reflexivity
end;

opaque symbol eta_exp_∃ [a : Set] (f : τ (a ⤳ o)) : 
    π(∃ f = `∃ x, f x)≔
begin
    assume a f;
    rewrite .[x in ∃ x = _] eta_exp f;
    reflexivity
end;

opaque symbol ¬∀=∃¬ (t : Set) (p : τ (t ⤳ o)) : 
    π (¬(∀ p) = (`∃ (x : τ t), ¬ (p x)))≔
begin
assume t p;
refine propExt (¬ (∀ p)) (`∃ x, ¬ (p x)) _ _
{assume h;
    refine ∨ₑ (em (`∃ x, ¬ p x)) _ _
    {assume he; refine he}
    {assume hne;
        have forall_p : Π x : τ t, π (p x)
            {assume a; refine ¬¬ₑ (p a) (λ hp, hne (∃ᵢ [t] [λ y, ¬ p y] a hp))};
        have forall_p2 : π (∀ p)
            {rewrite eta_exp p; refine forall_p};
        refine ⊥ₑ (h forall_p2)}}
{assume h h2;
    refine ∃ₑ h _;
    assume x h1;
    have forAll_x_p : Π x, π (p x)
        {assume y;
        refine (=⇒ (eta_exp_∀ p) h2) y};
    refine h1 (forAll_x_p x)}
end;

opaque symbol ¬∃=∀¬ (t : Set) (p : τ t → τ o) : 
    π (¬(∃ p) = (`∀ (x : τ t), ¬ p x))≔     
begin
assume t p;
refine propExt (¬ (∃ p)) (`∀ x, ¬ p x) _ _
    {assume h a ha; 
    have H0: π (∃ p)
        {rewrite eta_exp_∃; refine (∃ᵢ [t] [p] a ha)};
    refine h H0}
    {assume h1 h2; 
    refine ∃ₑ [t] [p] (=⇒ (eta_exp_∃ p) h2) (λ a ha, (h1 a) ha)}
end;


// Skolemisazion

opaque symbol εᵢ_rev :  Π [a: Set], Π p: (τ a → Prop),  
    π (p (ε p)) → π (∃ p)≔
begin
    assume a p h;
    refine =⇒ (eq_sym (eta_exp_∃ p)) (∃ᵢ [a] [p] (ε p) h)
end;

opaque symbol ∃_skolem (a: Set) (p: τ (a ⤳ o)) :  
    π ((∃ p) = (p (ε p)))≔
begin
    assume a p;
    refine propExt (∃ p) (p (ε p)) (εᵢ [a] p) (εᵢ_rev [a] p)
end;

opaque symbol ∀_skolem (a: Set) (p: τ (a ⤳ o)) :  
    π (¬ (∀ p) = ¬ (p (ε (λ x, ¬ (p x)))))≔
begin
    assume a p;
    rewrite ¬∀=∃¬;
    refine  propExt (`∃ x, ¬ (p x)) (¬ (p (ε (λ x, ¬ (p x))))) _ _
        {assume h; refine ind_eq (eq_sym (∃_skolem a (λ x, ¬ (p x)))) (λ x, x) h}
        {assume h; refine ind_eq (∃_skolem a (λ x, ¬ (p x))) (λ x, x) h}
end;


// Quantifier Distributivity

opaque symbol ∀∧_dist_r t a (p : τ(t ⤳ o)): π ((a ∧ ∀ p) = (`∀ x, a ∧ p x))≔
begin
    assume t a p;
    refine propExt (a ∧ ∀ p) (∀(λ x, a ∧ p x)) _ _
        {assume h x;
        refine ∧ᵢ (∧ₑ₁ h) ((=⇒ (eta_exp_∀ p) (∧ₑ₂ h)) x)}
        {assume h;
        refine ∨ₑ (em (∀ p)) _ _
            {assume h1;
            refine ∧ᵢ (∧ₑ₁ (h (el t))) h1}
            {assume h1;
            have H0: π (¬ (p (ε (λ x, ¬ (p x)))))
                {refine =⇒ (∀_skolem t p) h1};
            have H1: π (p (ε (λ x, ¬ (p x))))
                {refine ∧ₑ₂ (h (ε (λ x, ¬ (p x))))};
            refine ⊥ₑ (H0 H1)}}
end;

opaque symbol ∀∧_dist_l t a (p : τ(t ⤳ o)): π ((∀ p ∧ a) = (`∀ x,p x ∧ a))≔
begin
    assume t a p;
    refine propExt (∀ p ∧ a) (`∀ x, p x ∧ a) _ _
        {assume h0 x;
        rewrite ∧_com;
        refine (=⇒ ((∀∧_dist_r t a p)) (=⇒ (∧_com (∀ p) a) h0)) x
        }
        {assume h0;
        rewrite ∧_com;
        have H0: π (`∀ x, a ∧ p x)
            {assume x;
            rewrite ∧_com;
            refine h0 x};
        refine =⇒ (eq_sym (∀∧_dist_r t a p)) H0
        };
end;

opaque symbol ∀∨_dist_r t a (p : τ(t ⤳ o)): π ((a ∨ ∀ p) = (`∀ x, a ∨ p x))≔
begin
    assume t a p;
    refine propExt (a ∨ ∀ p) (∀(λ x, a ∨ p x)) _ _
        {assume h x;
        refine ∨ₑ h _ _
            {assume h0;
            refine ∨ᵢ₁ h0}
            {assume h0;
            refine ∨ᵢ₂ ((=⇒ (eta_exp_∀ p) h0) x)}}
        {assume h;
        refine ∨ₑ (em (∀ p)) _ _
            {assume h1;
            refine ∨ᵢ₂ h1}
            {assume h1;
            have H0: π (¬ (p (ε (λ x, ¬ (p x)))))
                {refine =⇒ (∀_skolem t p) h1};
            refine ∨ₑ (h (ε (λ x, ¬ (p x)))) _ _
                {assume h0;
                refine ∨ᵢ₁ h0}
                {assume h0;
                refine ⊥ₑ (H0 h0)}}}
end;

opaque symbol ∀∨_dist_l t a (p : τ(t ⤳ o)): π ((∀ p ∨ a) = (`∀ x,p x ∨ a))≔
begin
    assume t a p;
    refine propExt (∀ p ∨ a) (`∀ x,p x ∨ a) _ _
        {assume h0 x;
        rewrite ∨_com;
        refine (=⇒ ((∀∨_dist_r t a p)) (=⇒ (∨_com (∀ p) a) h0)) x}
        {assume h0;
        rewrite ∨_com;
        have H0: π (`∀ x, a ∨ p x)
            {assume x;
            rewrite ∨_com;
            refine h0 x};
        refine =⇒ (eq_sym (∀∨_dist_r t a p)) H0};
end;

opaque symbol ∀_ext [t: Set] [p q] : π(`∀ (x : τ t), p x = q x) → π ((`∀ (x: τ t), p x) = (`∀ (x: τ t), q x))≔
begin
    assume t p q h;
    refine propExt (`∀ (x: τ t), p x) (`∀ (x: τ t), q x) _ _
        {assume h1 x;
        refine =⇒ (h x) (h1 x)}
        {assume h1 x;
        refine =⇒ (eq_sym (h x)) (h1 x)}
end;