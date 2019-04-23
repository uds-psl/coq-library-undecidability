From Undecidability.L.Tactics Require Export LTactics GenEncode.
From Undecidability.L.Datatypes Require Export LNat LProd Lists.
From Undecidability Require Export FOL.BPCP_FOL.

Instance registered_BSRS : registered BSRS.
Proof.
  unfold BSRS, stack, card. exact _.
Defined.

Hint Extern 0 (L.app (L.app (@enc (@BSRS) _ _) _) _ >( _ ) _)=> apply list_enc_correct : Lrewrite.


Run TemplateProgram (tmGenEncode "term_enc" term).

Instance computable_V : computable V.
Proof.
  extract constructor.
Defined.

Instance computable_t_e : computable t_e.
Proof.
  extract constructor.
Defined.

Instance computable_t_f : computable t_f.
Proof.
  extract constructor.
Defined.

Inductive form' : Set :=
  Pr' : term -> term -> form' 
| Q' : form' 
| Fal' : form' 
| Impl' :form' -> form' -> form'
| All' : nat -> form' -> form'.

Run TemplateProgram (tmGenEncode "form'_enc" form').
Hint Rewrite form'_enc_correct : Lrewrite.

Fixpoint form_to_form' {b} (phi : form b) :=
  match phi with
  | Pr s t => Pr' s t
  | Q => Q'
  | Fal => Fal'
  | Impl phi psi => Impl' (form_to_form' phi) (form_to_form' psi)
  | All x phi => All' x (form_to_form' phi)
  end.            

Require Import Equations.Equations.

Instance registered_form {b} : registered (form b).
Proof.
  eapply (registerAs form_to_form').
  intros phi; induction phi; cbn; intros psi E.
  - now destruct psi; inv E.
  - now destruct psi; inv E.
  - depelim psi; try now inv E. Show Proof.
    inv H. eapply Eqdep_dec.inj_pair2_eq_dec in H1. now subst.
    intros. decide equality.
  - destruct psi; inv E. f_equal; eauto.
  - destruct psi; inv E. f_equal; eauto.
Defined. 

Instance computable_Pr {b} : computable (@Pr b).
Proof.
  extract constructor.
Qed.

Instance computable_Q {b} : computable (@Q b).
Proof.
  extract constructor.
Qed.

Instance computable_Fal : computable Fal.
Proof.
  extract constructor.
Qed.

Instance computable_Impl {b} : computable (@Impl b).
Proof.
  extract constructor.
Qed.

Instance computable_All {b} : computable (@All b).
Proof.
  extract constructor.
Qed.

Instance computable_fold_right X Y `{registered X} `{registered Y} : computable (@fold_right X Y).
Proof.
  extract.
Qed.

Instance computable_prep : computable prep.
Proof.
  extract.
Qed.

Instance computable_enc : computable enc.
Proof.
  extract.
Qed.

Definition mkPr {b : logic} '(x, y) := Pr (enc x) (enc y).

Instance computable_mkPr {b} : computable (@mkPr b).
Proof.
  extract.
Qed.
  
Instance computable_F1 {b} : computable (@F1 b).
Proof.
  change (@F1 b) with (fun (R : BSRS) => map mkPr R).
  extract.
Qed.  

Definition mkPr2 {b : logic} '(x,y) := ∀ 0; ∀ 1; Pr 0 1 --> Pr (prep x 0) (prep y 1).

Instance computable_mkPr2 {b} : computable (@mkPr2 b).
Proof.
  extract.
Qed.

Instance computable_F2 {b} : computable (@F2 b).
Proof.
  change (@F2 b) with (fun (R : BSRS) => map mkPr2 R).
  extract.
Qed.  

Instance computable_F3 {b} : computable (@F3 b).
Proof.
  typeclasses eauto.
Defined. 
           
Instance computable_impl {b} : computable (@impl b).
Proof.
  extract.
Qed.

Definition computable_F {b} : computable (@F b).
Proof.
  unfold F.
Abort.
(* Qed. *)
