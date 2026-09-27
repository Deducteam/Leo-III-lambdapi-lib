/* 
---------------------------------------------------------------------------
Library on User-Defined Tactics for Leo-III Verification
---------------------------------------------------------------------------

This file defines user-defined tactics used in the verification of
Leo-III proofs within Lambdapi. It introduces the abstract `Tactic`
type together with basic tactic combinators and derived strategies
for clausification steps, including:

  • Term simplification
  • Clausification including Skolemization and Quantifier transformations
  • Literal Normalization
---------------------------------------------------------------------------
*/

require open Stdlib.HOL Stdlib.Impred Stdlib.List Stdlib.String Stdlib.Univ Stdlib.Tactic Leo-III-lambdapi-lib.CNFeq Leo-III-lambdapi-lib.TptpArithmatic;

/******************************************************************************
 *  Setup for the user defined tactic         
 ******************************************************************************/

 symbol tactic : Set;
 rule τ tactic ↪ Tactic;

 notation #orelse infix left 10000;
 symbol #and ≔ &;
 
 symbol set0 : Set;
 rule τ set0 ↪ Set; 

 // needed for tactic terms over polymorphic proof-producing lemmas

 unif_rule @η $l $a ≡ Π x:$b, π $c.[x] ↪ [$l ≡ prop; $a ≡ `∀ x:$b, $c.[x]];
 unif_rule @η $l $a ≡ Π x:$b, @η prop $c.[x] ↪ [$l ≡ prop; $a ≡ `∀ x:$b, $c.[x]];


/******************************************************************************
 *  Tactic for Leo-III term simplification        
 ******************************************************************************/
  
symbol applyAny : 𝕃 tactic → Tactic;
 rule applyAny ($t0 ⸬ ($t1 ⸬ $tl)) ↪ $t0 #orelse (applyAny ($t1 ⸬ $tl))
 with applyAny ($t0 ⸬ □) ↪ $t0;
 
 symbol listOfAllSimpRules ≔ ((#rewrite "" "" ∨_idem) ⸬ (#rewrite "" "" em_eq_l) ⸬ (#rewrite "" "" em_eq_r) ⸬ (#rewrite "" "" ∨⊤) ⸬ 
     (#rewrite "" "" ⊤∨) ⸬ (#rewrite "" "" ∨⊥) ⸬ (#rewrite "" "" ⊥∨) ⸬ (#rewrite "" "" ∧_idem) ⸬ (#rewrite "" "" ∧_contra_r) ⸬ (#rewrite "" "" ∧_contra_l) ⸬ 
     (#rewrite "" "" ∧⊤) ⸬ (#rewrite "" "" ⊤∧) ⸬ (#rewrite "" "" ∧⊥) ⸬ (#rewrite "" "" ⊥∧) ⸬ (#rewrite "" "" ⇒⊤) ⸬ (#rewrite "" "" ⊥⇒) ⸬ (#rewrite "" "" ⊤⇒) ⸬ 
     (#rewrite "" "" ⇒⊥) ⸬ (#rewrite "" "" ⇒_refl) ⸬ (#rewrite "" "" ⇔⊤) ⸬ (#rewrite "" "" ⊤⇔) ⸬ (#rewrite "" "" ⊥⇔) ⸬ (#rewrite "" "" ⇔⊥) ⸬ 
     (#rewrite "" "" ⇔_refl) ⸬ (#rewrite "" "" ¬⊤) ⸬ (#rewrite "" "" ¬⊥) ⸬ (#rewrite "" "" ¬¬ₑ_eq) ⸬ (#rewrite "" "" =⊤) ⸬ (#rewrite "" "" ⊤=) ⸬ 
     (#rewrite "" "" =⊥) ⸬ (#rewrite "" "" ⊥=) ⸬ (#rewrite "" "" [prop] =_refl) ⸬ (#rewrite "" "" ¬=⊥) ⸬ (#rewrite "" "" ¬⊥=) ⸬ (#rewrite "" "" ¬=⊤) ⸬ 
     (#rewrite "" "" ¬⊤=) ⸬ (#rewrite "" "" [prop] ¬=_irrefl) ⸬ (#rewrite "" "" [prop] ∀_const) ⸬ (#rewrite "" "" [prop] ∃_const) ⸬ (#rewrite "" "" ¬x=_idem) ⸬ (#rewrite "" "" =¬x_idem) ⸬ 
     (#rewrite "" "" [prop] polarity_switch) ⸬ (#refine "⊤ᵢ") ⸬ □);
     // the rules and ... are added as Leo omits trivially false literals, we account for this using this rule
 
 symbol applyAllSimplifications ≔ #repeat (applyAny listOfAllSimpRules #orelse #simplify_beta);

 symbol applyAllSimplificationsOnce ≔ applyAny listOfAllSimpRules;

 // version of the tactic also applying the arithmatic rules

 symbol listOfAllArithRules ≔ ((#rewrite "" "" [prop] (tptp_difference_simp [tptp_int])) ⸬ (#rewrite "" "" [prop] (tptp_lesseq_simp [tptp_int])) ⸬ 
      (#rewrite "" "" [prop] (tptp_greater_simp [tptp_int])) ⸬ (#rewrite "" "" [prop] (tptp_greatereq_simp [tptp_int])) ⸬

      (#rewrite "" "" [prop] (tptp_difference_simp [tptp_rat])) ⸬ (#rewrite "" "" [prop] (tptp_lesseq_simp [tptp_rat])) ⸬ 
      (#rewrite "" "" [prop] (tptp_greater_simp [tptp_rat])) ⸬ (#rewrite "" "" [prop] (tptp_greatereq_simp [tptp_rat])) ⸬

      (#rewrite "" "" [prop] (tptp_difference_simp [tptp_real])) ⸬ (#rewrite "" "" [prop] (tptp_lesseq_simp [tptp_real])) ⸬ 
      (#rewrite "" "" [prop] (tptp_greater_simp [tptp_real])) ⸬ (#rewrite "" "" [prop] (tptp_greatereq_simp [tptp_real])) ⸬ □);

 symbol applyAllSimplificationsWithArithmatic ≔ #repeat ((applyAny listOfAllSimpRules #orelse applyAny listOfAllArithRules) #orelse #simplify_beta);

 symbol applyAllSimplificationsWithArithmaticOnce ≔ (applyAny listOfAllSimpRules #orelse applyAny listOfAllArithRules);

/******************************************************************************
*  Definition of Leo-III literal normalization
******************************************************************************/

symbol applyAnyAtPos : String → 𝕃 (string ⤳ tactic) → Tactic;
rule applyAnyAtPos $pat ($t0 ⸬ ($t1 ⸬ $tl)) ↪ ($t0 $pat) #orelse (applyAnyAtPos $pat ($t1 ⸬ $tl))
with applyAnyAtPos $pat ($t0 ⸬ □) ↪ $t0 $pat;

symbol LitNormRules ≔ 
    (λ pat: String, (#rewrite "" pat =⊤)) ⸬ (λ pat: String, (#rewrite "" pat ⊤=)) ⸬ 
    (λ pat: String, (#rewrite "" pat =⊥)) ⸬ (λ pat: String, (#rewrite "" pat ⊥=)) ⸬
    (λ pat: String, (#rewrite "" pat [prop] polarity_switch)) ⸬ (λ pat: String, (#rewrite "" pat [prop] =_refl)) ⸬ □;


symbol normalizeTerms ≔ #and (#and (#repeat (#rewrite "" "" ¬⊥)) (#repeat (#rewrite "" "" ¬⊤))) (#repeat (#rewrite "" "" ¬¬ₑ_eq));

symbol normalizeEqLit ≔ 
#and
  normalizeTerms
  (#and
    (#and 
      (#and ((#repeat (applyAnyAtPos ".[x in x = _]" LitNormRules)))
            (#repeat (applyAnyAtPos ".[x in _ = x]" LitNormRules)))
      (#and ((#repeat (applyAnyAtPos ".[x in ¬ x = _]" LitNormRules)))
            (#repeat (applyAnyAtPos ".[x in _ = ¬ x]" LitNormRules))))
    normalizeTerms)
;

symbol close= ≔ (#and (#rewrite "" ".[x in x]" (=_refl o)) (#refine "⊤ᵢ"));

symbol closeEq (t: Set) ≔
(close= #orelse (#and (#rewrite "" ".[x in x = _]" [prop] (=_sym [t])) close=) #orelse (#and (#rewrite "" ".[x in ¬ x = _]" [prop] (=_sym [t])) close=));


/******************************************************************************
*  Definition of Leo-III clausification tactic        
******************************************************************************/

// Boolean identities

symbol normAsso ≔ #repeat ((#rewrite "" "" [prop] ∧_assoc) #orelse (#rewrite "" "" [prop] ∨_assoc));

symbol normAsso_∨ ≔ #repeat (#rewrite "" "" [prop] ∨_assoc);

symbol normAsso_∧ ≔ #repeat (#rewrite "" "" [prop] ∧_assoc);

symbol allCNFids_list ≔ ((#rewrite "" "" [prop] deMorgan_∧) ⸬ (#rewrite "" "" [prop] deMorgan_∨) ⸬ (#rewrite "" "" [prop] ⇒=∨) ⸬ (#rewrite "" "" [prop] ¬⇒=∧¬) ⸬ (#and (#rewrite "" "" [prop] ∧∨_dist_l) normAsso) ⸬ (#and (#rewrite "" "" [prop] ∧∨_dist_r) normAsso) ⸬ (#rewrite "" "" ¬¬ₑ_eq) ⸬ (#rewrite "" "" [prop] ∨_assoc) ⸬ (#rewrite "" "" [prop] ∧_assoc) ⸬ □);

symbol boolIds ≔ (applyAny allCNFids_list);

symbol onlyBoolIds ≔ #and (#repeat boolIds) #reflexivity;


// skolemisazion

symbol skolemProzess_∃ sk_def : Tactic ≔ (#and (#and (#rewrite "" "" [prop] ∃_skolem) #simplify_beta) sk_def);

symbol skolemProzess_∀ sk_def : Tactic ≔ (#and (#and (#rewrite "" "" [prop] ∀_skolem) #simplify_beta) sk_def);

symbol skolemProzess sk_def : Tactic ≔ (skolemProzess_∀ sk_def) #orelse (skolemProzess_∃ sk_def);

symbol stepwise_skolem0: 𝕃 tactic → Tactic;
rule stepwise_skolem0 ($sk1 ⸬ ($sk2 ⸬ $sk3)) ↪ #repeat ((#and (skolemProzess $sk1) (stepwise_skolem0 ($sk2 ⸬ $sk3))) #orelse boolIds)
with stepwise_skolem0 ($sk1 ⸬ □) ↪ #and (#repeat ((skolemProzess $sk1) #orelse boolIds)) #reflexivity;

symbol stepwise_skolem: (Tactic → Tactic) → 𝕃 tactic → Tactic;
rule stepwise_skolem $t ($sk1 ⸬ ($sk2 ⸬ $sk3)) ↪ #repeat ((#and ($t $sk1) (stepwise_skolem $t ($sk2 ⸬ $sk3))) #orelse boolIds)
with stepwise_skolem $t ($sk1 ⸬ □) ↪ #and (#repeat (($t $sk1) #orelse boolIds)) #reflexivity;


// handling universal quantification

symbol stepwise_quants: 𝕃 tactic → Tactic;
rule stepwise_quants ($sk1 ⸬ ($sk2 ⸬ $sk3)) ↪ #repeat ((#and $sk1 (stepwise_quants ($sk2 ⸬ $sk3))) #orelse boolIds)
with stepwise_quants ($sk1 ⸬ □) ↪ #and (#repeat ($sk1 #orelse boolIds)) #reflexivity;

symbol move_∀_out_dijs ≔ #repeat (#rewrite "" "" [prop] ∀∨_dist_r) #orelse (#rewrite "" "" [prop] ∀∨_dist_l);

symbol move_∀_out [l] [assumeTy:U l] (assumeVar: String) : Tactic ≔ ((#and (#and (((#and (#repeat  (#rewrite "" ".[x in x = _]" ¬¬ₑ_eq)) (#refine "∀_ext _"))) #orelse (#refine "∀_ext _")) (#simplify_beta)) (#assume assumeVar [l] [assumeTy] (λ X:η assumeTy, nothing))) #orelse ((#rewrite "" "" [prop] ∀∧_dist_r) #orelse (#rewrite "" "" [prop] ∀∧_dist_l) #orelse (#rewrite "" "" [prop] ∀∨_dist_r) #orelse (#rewrite "" "" [prop] ∀∨_dist_l)));

symbol move_¬∃_out [l] [assumeTy:U l] (assumeVar: String) : Tactic ≔ (#and (#rewrite "" "" [prop] ¬∃=∀¬) (move_∀_out [l] [assumeTy] assumeVar));


/******************************************************************************
 *  Implicit Transformations         
 ******************************************************************************/

// Identification of trivially false literals with ⊥
symbol removeTrivialFalse (pattern: String) ≔ #try ((#rewrite "" pattern [prop] ¬=_irrefl) #orelse (#rewrite "" pattern ¬⊤));

// Normalisation of eqational literals with ⊤ or ⊥ on one side to non-equational ones
symbol normalizeLiteral (pattern: String) ≔ (#rewrite "" pattern =⊤) #orelse (#rewrite "left" pattern =⊤) #orelse (#rewrite "" pattern =⊥) #orelse (#rewrite "left" pattern =⊥); 
