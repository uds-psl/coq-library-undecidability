(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Bool Eqdep_dec.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations utils fol_ops.

Set Implicit Arguments.

Definition decidable (P : Prop) := { P } + { ~ P }.

Section decidable_fun_pos_bool.

  (** Decidability of quantification over extensional and
      decidable predicates of type (pos n -> bool) -> Prop *)

  Variable (n : nat) (K : (pos n -> bool) -> Prop)
           (HK : forall P Q, (forall x, P x = Q x) -> K P <-> K Q)
           (D : forall P, decidable (K P)).

  Let Dfa : decidable (forall v, K (vec_pos v)).
  Proof.
    apply (fol_quant_sem_dec fol_fa).
    + apply finite_t_vec, finite_t_bool.
    + intros v; apply D.
  Qed.

  Let Dex : decidable (exists v, K (vec_pos v)).
  Proof.
    apply (fol_quant_sem_dec fol_ex).
    + apply finite_t_vec, finite_t_bool.
    + intros v; apply D.
  Qed.

  Theorem fa_fun_pos_bool_decidable : decidable (forall P, K P).
  Proof.
    destruct Dfa as [ H | H ].
    + left. 
      intros P; generalize (H (vec_set_pos P)).
      apply HK; intro; rew vec.
    + right; contradict H.
      intro; apply H.
  Qed.

  Theorem ex_fun_pos_bool_decidable : decidable (exists P, K P).
  Proof.
    destruct Dex as [ H | H ].
    + left.
      destruct H as (v & Hv).
      exists (vec_pos v); auto.
    + right; contradict H.
      destruct H as (P & HP).
      exists (vec_set_pos P).
      revert HP; apply HK.
      intro; rew vec. 
  Qed.

End decidable_fun_pos_bool.

Section decidable_fun_finite_bool.

  (** Decidability of quantification over extensional and decidable
      predicates of type (X -> bool) -> Prop when 
      X is a finite and discrete type *)

  Variable (X : Type) (H1 : finite_t X) (H2 : discrete X)
           (K : (X -> bool) -> Prop)
           (HK : forall P Q, (forall x, P x = Q x) -> K P <-> K Q)
           (Dec : forall P, decidable (K P)).

  Let D : { n : nat & bij_t X (pos n) }.
  Proof.
    apply finite_t_discrete_bij_t_pos; auto.
  Qed.

  Let n := projT1 D.
  Let i : X -> pos n := projT1 (projT2 D).
  Let j : pos n -> X := proj1_sig (projT2 (projT2 D)).

  Let Hji : forall x, j (i x) = x.
  Proof. apply (proj2_sig (projT2 (projT2 D))). Qed.

  Let Hij : forall y, i (j y) = y.
  Proof. apply (proj2_sig (projT2 (projT2 D))). Qed.

  Let T P := K (fun p => P (i p)).

  Let T_ext P Q : (forall x, P x = Q x) -> T P <-> T Q.
  Proof. intros H; apply HK; intro; apply H. Qed.

  Let T_dec P : decidable (T P).
  Proof. apply Dec. Qed.

  Theorem fa_fun_bool_decidable : decidable (forall P, K P).
  Proof.
    assert (H : decidable (forall P, T P)).
    { apply fa_fun_pos_bool_decidable; auto. }
    destruct H as [ H | H ]; [ left | right ].
    + intros P.
      generalize (H (fun p => P (j p))).
      apply HK; intro; rewrite Hji; auto.
    + contradict H; intros P; apply H.
  Qed.

  Theorem ex_fun_bool_decidable : decidable (exists P, K P).
  Proof.
    assert (H : decidable (exists P, T P)).
    { apply ex_fun_pos_bool_decidable; auto. }
    destruct H as [ H | H ]; [ left | right ].
    + destruct H as (P & H).
      exists (fun x => P (i x)); auto.
    + contradict H.
      destruct H as (P & H).
      exists (fun p => P (j p)).
      revert H; apply HK.
      intro; rewrite Hji; auto.
  Qed.

End decidable_fun_finite_bool.

Section decidable_upto.

  (** decidability of existential quantification 
      for P : X -> Prop when X is finite upto some
      binary relation R which is a morphism for P *)

  Variable (X : Type) (R : X -> X -> Prop) 
           (P : X -> Prop) (HP : forall x, decidable (P x))
           (HR : forall x y, R x y -> P x <-> P y).

  Theorem decidable_list_upto_fa l :
             (forall x, exists y, In y l /\ R x y)
          -> decidable (forall x, P x).
  Proof.
    intros Hl.
    destruct list_dec with (P := fun x => ~ P x) (Q := P) (l := l)
      as [ (x & H1 & H2) | H ].
    + intros x; generalize (HP x); unfold decidable; tauto.
    + right; contradict H2; auto.
    + left; intros x.
      destruct (Hl x) as (y & H1 & H2).
      generalize (H _ H1); apply (HR H2).
  Qed.

  Theorem decidable_list_upto_ex l :
             (forall x, exists y, In y l /\ R x y)
          -> decidable (exists x, P x).
  Proof.
    intros Hl.
    destruct list_dec with (1 := HP) (l := l)
      as [ (x & H1 & H2) | H ].
    + left; exists x; auto.
    + right; intros (x & Hx).
      destruct (Hl x) as (y & H1 & H2).
      apply (H _ H1). 
      revert Hx; apply (HR H2).
  Qed.

End decidable_upto.

Definition fun_ext X Y (f g : X -> Y) := forall x, f x = g x.
Definition prop_ext X (f g : X -> Prop) := forall x, f x <-> g x.

Section fun_pos_finite_t_upto.

  (** If X is finite then pos n -> X is finite upto
      extensional equality *)

  Variable (X : Type) (HX : finite_t X).
 
  Theorem fun_pos_finite_t_upto n : finite_t_upto (pos n -> X) (@fun_ext _ _).
  Proof.
    assert (H : finite_t (vec X n)).
    { apply finite_t_vec; auto. }
    destruct H as (l & Hl).
    exists (map (@vec_pos _ _) l).
    intros f. 
    exists (vec_pos (vec_set_pos f)); split.
    + apply in_map_iff; exists (vec_set_pos f); auto.
    + intros p; rew vec.
  Qed.

End fun_pos_finite_t_upto.

Section fun_finite_t_upto.

  (** If X is finite and discrete and Y is finite that 
      X -> Y is finite upto extensional equality *)

  Variable (X : Type) (HX1 : finite_t X) (HX2 : discrete X)
           (Y : Type) (HY : finite_t Y).

  Let D : { n : nat & bij_t X (pos n) }.
  Proof.
    apply finite_t_discrete_bij_t_pos; auto.
  Qed.

  Theorem fun_finite_t_upto : finite_t_upto (X -> Y) (@fun_ext _ _).
  Proof.
    destruct finite_t_discrete_bij_t_pos with X
      as (n & i & j & Hji & Hij); auto.
    destruct fun_pos_finite_t_upto with Y n
      as (l & Hl); auto.
    exists (map (fun f x => f (i x)) l).
    intros f.
    destruct (Hl (fun p => f (j p))) as (g & H1 & H2).
    exists (fun x => g (i x)); split.
    + apply in_map_iff; exists g; auto.
    + intros x.
      red in H2.
      rewrite <- (Hji x) at 1; auto.
  Qed.

End fun_finite_t_upto.

Section dec_pred_finite_t_upto.

  (** If X is finite and discrete then decidable
      predicates of type X -> Prop are finitely
      many upto extensional equivalence *) 

  Variable (X : Type) (HX1 : finite_t X) (HX2 : discrete X).

  Hint Resolve finite_t_bool.

  Let bool_prop (f : X -> bool) : { p : X -> Prop & forall x, decidable (p x) }.
  Proof.
    exists (fun x => f x = true).
    intro; apply bool_dec.
  Defined.

  Theorem pred_finite_t_upto : finite_t_upto { p : X -> Prop & forall x, decidable (p x) }
                               (fun p q => prop_ext (projT1 p) (projT1 q)).
  Proof.
    destruct fun_finite_t_upto with X bool as (l & Hl); auto.
    exists (map bool_prop l).
    intros (p & Hp).
    destruct (Hl (fun x => if Hp x then true else false)) as (f & H1 & H2).
    exists (bool_prop f); split.
    + apply in_map_iff; exists f; auto.
    + simpl; intros x; red in H2.
      rewrite <- H2.
      destruct (Hp x); split; auto; discriminate.
  Qed.

End dec_pred_finite_t_upto.

Section finite_t_valuations.

  (** For a given list of variables ln : list nat, and X a finite,
      discrete and inhabited type, there are finitely many
      valuations of type nat -> X, upto to equality over ln *)

  Variable (X : Type) 
           (HX1 : finite_t X)
           (HX2 : discrete X) (x : X).

  Implicit Type (ln : list nat).

  Let R ln (f g : nat -> X) := forall n, In n ln -> f n = g n.

  Let combine (n : nat) : (X * (nat -> X)) -> nat -> X.
  Proof.
    intros (x', f) m.
    destruct (eq_nat_dec n m).
    + exact x'.
    + apply (f m).
  Defined.

  Theorem finite_t_valuations ln : finite_t_upto _ (R ln).
  Proof.
    induction ln as [ | n ln IH ].
    + exists ((fun _ => x)::nil).
      intros f; exists (fun _ => x); split; simpl; auto.
      intros ? [].
    + destruct HX1 as (l & Hl).
      destruct IH as (m & Hm).
      exists (map (combine n) (list_prod l m)).
      intros f.
      destruct (Hm f) as (g & H1 & H2).
      exists (combine n (f n,g)); split.
      * apply in_map_iff; exists (f n,g); split; auto.
        apply list_prod_spec; auto.
      * intros n' [ <- | Hn' ].
        - unfold combine.
          destruct (eq_nat_dec n n) as [ | [] ]; auto.
        - unfold combine.
          destruct (eq_nat_dec n n') as [ E | D ]; auto.
  Qed.

End finite_t_valuations.

Section finite_t_model.

  (** For a given list of symbols ls : list syms, where syms is
      a discrete type, and a type X, finite and discrete, 
      and a type Y, finite and inhabited, 
      there are finitely many valuations of type
 
                 forall s, vec X (ar s) -> Y, 

      upto to extensional equality over the list ls *)

  Variable (syms : Type) (ar : syms -> nat) (Hsyms : discrete syms)
           (X : Type) (HX1 : finite_t X) (HX2 : discrete X)
           (Y : Type) (HY : finite_t Y) (y : Y).

  Implicit Type (ls : list syms).

  (* Extensionnal equality over ls *)

  Let funs := forall s, vec X (ar s) -> Y.

  Let R ls (s1 s2 : funs) := 
        forall s, In s ls -> forall v, @s1 s v = s2 s v.

  Hint Resolve finite_t_vec vec_eq_dec.

  Let fun_combine s (f : vec X (ar s) -> Y) (g : funs) : funs.
  Proof.
    intros s'.
    destruct (Hsyms s s').
    + subst s; exact f.
    + apply g.
  Defined. 

  Theorem finite_t_model ls : finite_t_upto funs (R ls).
  Proof.
    induction ls as [ | s ls IH ].
    + exists ((fun _ _ => y) :: nil).
      intros f; exists (fun _ _ => y); split; simpl; auto.
      intros ? [].
    + destruct IH as (m & Hm).
      destruct fun_finite_t_upto with (vec X (ar s)) Y
        as (l & Hl); auto.
      exists (map (fun p => fun_combine (fst p) (snd p)) (list_prod l m)).
      intros f.
      destruct (Hl (f s)) as (f' & H1 & H2).
      destruct (Hm f) as (g & H3 & H4).
      exists (fun_combine f' g); split.
      * apply in_map_iff; exists (f',g); split; auto.
        apply list_prod_spec; simpl; auto.
      * intros s' [ <- | Hs ] v.
        - red in H2; rewrite H2.
           unfold fun_combine.
           destruct (Hsyms s s) as [ E | [] ]; auto.
           rewrite (UIP_dec Hsyms E eq_refl); auto.
        - unfold fun_combine.
          destruct (Hsyms s s') as [ E | D ].
          ++ subst; cbn; apply H2.
          ++ apply H4; auto.
  Qed.

End finite_t_model.
