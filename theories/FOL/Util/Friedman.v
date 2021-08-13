Require Import List Lia.
From Undecidability.FOL.Util Require Import Syntax Syntax_facts FullTarski FullTarski_facts FullDeduction_facts FullDeduction.
Import Vector.VectorNotations.

Section Signature.

  
 (* Assume some signature and corresponding arity functions *)
 Context {Σ_funcs : funcs_signature}.
 Context {Σ_preds : preds_signature}.
 
 Variable Σ_funcs_ar : Σ_funcs -> nat.
 Variable Σ_preds_ar : Σ_preds -> nat.

 
Section Expanded.

  (* Add one more 0-ary predicate (i.e. propositional variable) to the predicates *)
  Inductive new_preds : Type :=
    Q_ : new_preds
  | old_preds (P : Σ_preds) : new_preds. 

  Definition new_preds_ar (P : new_preds) :=
    match P with
    | Q_ => 0
    | old_preds P => Σ_preds_ar P
    end.

  Instance funcs_signature : funcs_signature :=
    {| syms := Σ_funcs ; ar_syms := Σ_funcs_ar |}.

  Instance preds_signature : preds_signature :=
    {| preds := new_preds ; ar_preds := new_preds_ar |}.


  Definition Q {ff} := (@atom funcs_signature preds_signature _ ff Q_ ([])).
  Definition DN_Q {ff} phi : form := (phi ~> @Q ff) ~> Q.

  Fixpoint Friedman {ff} (phi : @form funcs_signature preds_signature _ ff) : form ff :=
    match phi with
    | falsity => Q
    | atom P v => match P with Q_ => Q | _ => DN_Q (atom P v) end
    | bin Impl phi psi => (Friedman phi) ~> (Friedman psi)
    | bin Conj phi psi => (Friedman phi) ∧ (Friedman psi)
    | bin Disj phi psi => DN_Q ((Friedman phi) ∨ (Friedman psi))
    | quant All phi => ∀ (Friedman phi)
    | quant Ex phi => DN_Q (∃ (Friedman phi))
    end.

                      
  Notation "'Fr' f" := (Friedman f) (at level 30).
  
  Variable ff : falsity_flag.
  Fixpoint List_Fr Gamma := map Friedman Gamma.
  
  Lemma DNE_Q Gamma phi : Gamma ⊢I Fr (DN_Q phi) ~> Fr phi. 
  Proof. Admitted.

  Lemma Friedman_cl_to_intu Gamma phi : Gamma ⊢C phi -> (List_Fr Gamma) ⊢I Fr phi.
  Proof. Admitted.

    
End Expanded.
End Signature.
