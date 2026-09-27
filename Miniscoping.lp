// Equalities for backward replay of Leo-III Miniscope steps.

// Each equality is oriented from the child goal toward its recorded parent.

require open Stdlib.PropExt Stdlib.FunExt Leo-III-lambdapi-lib.CNFeq;

// Rules for ∧

opaque symbol ∀∧ (t : Set) (p q : τ t → Prop) : π (((∀ p) ∧ (∀ q)) = (`∀ (x : τ t), p x ∧ q x)) ≔
begin
assume t p q;
have eta_p : π (p = (λ x, p x))
 { refine funExt p (λ x, p x) (λ x, eq_refl (p x)) };
rewrite eta_p;
have eta_q : π (q = (λ x, q x))
 { refine funExt q (λ x, q x) (λ x, eq_refl (q x)) };
rewrite eta_q;
refine propExt _ _ _ _
 {assume h x; refine ∧ᵢ ((∧ₑ₁ h) x) ((∧ₑ₂ h) x)}
 {assume h; refine ∧ᵢ (λ x, ∧ₑ₁ (h x)) (λ x, ∧ₑ₂ (h x))}
end;

opaque symbol ∃∧_l (t : Set) (p : τ t → Prop) (a : Prop) : π (((∃ p) ∧ a) = (`∃ (x : τ t), p x ∧ a)) ≔
begin
assume t p a;
have eta_p : π (p = (λ x, p x))
 { refine funExt p (λ x, p x) (λ x, eq_refl (p x)) };
rewrite eta_p;
refine propExt _ _ _ _
 {assume h; refine ∃ₑ (∧ₑ₁ h) (λ x hx, ∃ᵢ x (∧ᵢ hx (∧ₑ₂ h)))}
 {assume h; refine ∃ₑ h (λ x hx, ∧ᵢ (∃ᵢ x (∧ₑ₁ hx)) (∧ₑ₂ hx))}
end;

opaque symbol ∃∧_r (t : Set) (p : τ t → Prop) (a : Prop) : π ((a ∧ (∃ p)) = (`∃ (x : τ t), a ∧ p x)) ≔
begin
assume t p a;
have eta_p : π (p = (λ x, p x))
 { refine funExt p (λ x, p x) (λ x, eq_refl (p x)) };
rewrite eta_p;
refine propExt _ _ _ _
 {assume h; refine ∃ₑ (∧ₑ₂ h) (λ x hx, ∃ᵢ x (∧ᵢ (∧ₑ₁ h) hx))}
 {assume h; refine ∃ₑ h (λ x hx, ∧ᵢ (∧ₑ₁ hx) (∃ᵢ x (∧ₑ₂ hx)))}
end;

// Rules for ∨

opaque symbol ∃∨ (t : Set) (p q : τ t → Prop) : π (((∃ p) ∨ (∃ q)) = (`∃ (x : τ t), p x ∨ q x)) ≔
begin
assume t p q;
have eta_p : π (p = (λ x, p x))
 { refine funExt p (λ x, p x) (λ x, eq_refl (p x)) };
rewrite eta_p;
have eta_q : π (q = (λ x, q x))
 { refine funExt q (λ x, q x) (λ x, eq_refl (q x)) };
rewrite eta_q;
refine propExt _ _ _ _
 {assume h; refine ∨ₑ h (λ he, ∃ₑ he (λ x hx, ∃ᵢ x (∨ᵢ₁ hx))) (λ he, ∃ₑ he (λ x hx, ∃ᵢ x (∨ᵢ₂ hx)))}
 {assume h; refine ∃ₑ h (λ x hx, ∨ₑ hx (λ hp, ∨ᵢ₁ (∃ᵢ x hp)) (λ hq, ∨ᵢ₂ (∃ᵢ x hq)))}
end;

opaque symbol ∃∨_l (t : Set) (p : τ t → Prop) (a : Prop) : π (((∃ p) ∨ a) = (`∃ (x : τ t), p x ∨ a)) ≔
begin
assume t p a;
have eta_p : π (p = (λ x, p x))
 { refine funExt p (λ x, p x) (λ x, eq_refl (p x)) };
rewrite eta_p;
refine propExt _ _ _ _
 {assume h; refine ∨ₑ h (λ he, ∃ₑ he (λ x hx, ∃ᵢ x (∨ᵢ₁ hx))) (λ ha, ∃ᵢ (el t) (∨ᵢ₂ ha))}
 {assume h; refine ∃ₑ h (λ x hx, ∨ₑ hx (λ hp, ∨ᵢ₁ (∃ᵢ x hp)) (λ ha, ∨ᵢ₂ ha))}
end;

opaque symbol ∃∨_r (t : Set) (p : τ t → Prop) (a : Prop) : π ((a ∨ (∃ p)) = (`∃ (x : τ t), a ∨ p x)) ≔
begin
assume t p a;
have eta_p : π (p = (λ x, p x))
 { refine funExt p (λ x, p x) (λ x, eq_refl (p x)) };
rewrite eta_p;
refine propExt _ _ _ _
 {assume h; refine ∨ₑ h (λ ha, ∃ᵢ (el t) (∨ᵢ₁ ha)) (λ he, ∃ₑ he (λ x hx, ∃ᵢ x (∨ᵢ₂ hx)))}
 {assume h; refine ∃ₑ h (λ x hx, ∨ₑ hx (λ ha, ∨ᵢ₁ ha) (λ hp, ∨ᵢ₂ (∃ᵢ x hp)))}
end;

// Rules for ⇒

opaque symbol ∀⇒_l (t : Set) (p : τ t → Prop) (a : Prop) : π (((∃ p) ⇒ a) = (`∀ (x : τ t), p x ⇒ a)) ≔
begin
assume t p a;
have eta_p : π (p = (λ x, p x))
 { refine funExt p (λ x, p x) (λ x, eq_refl (p x)) };
rewrite eta_p;
refine propExt _ _ _ _
 {assume h x hx; refine h (∃ᵢ x hx)}
 {assume h he; refine ∃ₑ he (λ x hx, h x hx)}
end;

opaque symbol ∀⇒_r (t : Set) (p : τ t → Prop) (a : Prop) : π ((a ⇒ (∀ p)) = (`∀ (x : τ t), a ⇒ p x)) ≔
begin
assume t p a;
have eta_p : π (p = (λ x, p x))
 { refine funExt p (λ x, p x) (λ x, eq_refl (p x)) };
rewrite eta_p;
refine propExt _ _ _ _
 {assume h x ha; refine h ha x}
 {assume h ha x; refine h x ha}
end;

opaque symbol ∃⇒ (t : Set) (p q : τ t → Prop) : π (((∀ p) ⇒ (∃ q)) = (`∃ (x : τ t), p x ⇒ q x)) ≔
begin
assume t p q;
have eta_p : π (p = (λ x, p x))
 { refine funExt p (λ x, p x) (λ x, eq_refl (p x)) };
rewrite eta_p;
have eta_q : π (q = (λ x, q x))
 { refine funExt q (λ x, q x) (λ x, eq_refl (q x)) };
rewrite eta_q;
refine propExt _ _ _ _
 {assume h; refine ∨ₑ (em (`∀ x, p x)) _ _
   {assume hp; refine ∃ₑ (h hp) (λ x hx, ∃ᵢ x (λ _, hx))}
   {assume hn; refine ∃ₑ (∃¬ᵢ t p hn) (λ x hx, ∃ᵢ x (λ hp, ⊥ₑ (hx hp)))}}
 {assume h hp; refine ∃ₑ h (λ x hx, ∃ᵢ x (hx (hp x)))}
end;

opaque symbol ∃⇒_l (t : Set) (p : τ t → Prop) (a : Prop) : π (((∀ p) ⇒ a) = (`∃ (x : τ t), p x ⇒ a)) ≔
begin
assume t p a;
have eta_p : π (p = (λ x, p x))
 { refine funExt p (λ x, p x) (λ x, eq_refl (p x)) };
rewrite eta_p;
refine propExt _ _ _ _
 {assume h; refine ∨ₑ (em (`∀ x, p x)) _ _
   {assume hp; refine ∃ᵢ (el t) (λ _, h hp)}
   {assume hn; refine ∃ₑ (∃¬ᵢ t p hn) (λ x hx, ∃ᵢ x (λ hp, ⊥ₑ (hx hp)))}}
 {assume h hp; refine ∃ₑ h (λ x hx, hx (hp x))}
end;

opaque symbol ∃⇒_r (t : Set) (p : τ t → Prop) (a : Prop) : π ((a ⇒ (∃ p)) = (`∃ (x : τ t), a ⇒ p x)) ≔
begin
assume t p a;
have eta_p : π (p = (λ x, p x))
 { refine funExt p (λ x, p x) (λ x, eq_refl (p x)) };
rewrite eta_p;
refine propExt _ _ _ _
 {assume h; refine ∨ₑ (em a) _ _
   {assume ha; refine ∃ₑ (h ha) (λ x hx, ∃ᵢ x (λ _, hx))}
   {assume hn; refine ∃ᵢ (el t) (λ ha, ⊥ₑ (hn ha))}}
 {assume h ha; refine ∃ₑ h (λ x hx, ∃ᵢ x (hx ha))}
end;
