(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Bool.

From Undecidability.Shared.Libs.DLW 
  Require Import utils list_bool pos vec subcode sss.

From Undecidability.StackMachines 
  Require Export BSM.

Set Implicit Arguments.

Set Default Proof Using "Type".

Tactic Notation "rew" "length" := autorewrite with length_db.

Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).

(* ** Semantics results for BSM *)

Section Binary_Stack_Machine.

  Variable (n : nat).

  Notation "i // s -1> t" := (@bsm_sss n i s t).

  Ltac mydiscr := 
      match goal with H: ?x = _, G : ?x = _ |- _ => rewrite H in G; discriminate end.

  Ltac myinj := 
      match goal with H: ?x = _, G : ?x = _ |- _ => rewrite H in G; inversion G; subst; auto end.      
  
  (* bsm_sss is a functional relation *)
      
  Fact bsm_sss_fun i s t1 t2 : i // s -1> t1 -> i // s -1> t2 -> t1 = t2.
  Proof. intros []; subst; inversion 1; subst; auto; try mydiscr; myinj. Qed.

  (* bsm_sss is an informativelly total relation *) 
  
  Fact bsm_sss_total ii s : { t | ii // s -1> t }.
  Proof.
    destruct s as (i,v).
    destruct ii as [ x p q | x b ].
    + case_eq (v#>x); [ intros Hx | intros [] l Hx ].
      * exists (q,v); constructor; trivial.
      * exists (1+i,v[l/x]); constructor; trivial.
      * exists (p,v[l/x]); constructor; trivial.
    + exists (1+i,v[(b::v#>x)/x]); constructor.
  Qed.

  Fact bsm_sss_total' ii s : exists t, ii // s -1> t.
  Proof.
    destruct (bsm_sss_total ii s); firstorder.
  Qed.
  
  (* Hence computations can only stop at instructions which lie outside the code 
     Stalling means no instruction can be executed anymore. It DOES NOT mean
     that the state cannot change anymore (this is a strictly lesser requirement).
  *)
  
  Fact bsm_sss_stall : forall P s, sss_step_stall (@bsm_sss n) P s -> out_code (fst s) P.
  Proof.
    intros (i,P) (q,v) H; unfold fst.
    red in H.
    destruct (in_out_code_dec q (i,P)) as [ H1 | ]; auto; exfalso.
    apply in_code_subcode in H1.
    destruct H1 as (ii & l & r & H1 & H2).
    simpl in H1.
    destruct (bsm_sss_total ii (q,v)) as (t & Ht).
    apply (H t); subst; apply in_sss_step; auto.
  Qed.
 
  Notation "P // s -[ k ]-> t" := (sss_steps (@bsm_sss n) P k s t).
  Notation "P // s ->> t" := (sss_compute (@bsm_sss n) P s t).

  Fact bsm_compute_POP_E P i x p q v st :
         (i,POP x p q::nil) <sc P
      -> v#>x = nil
      -> P // (q,v) ->> st
      -> P // (i,v) ->> st.
  Proof.
    intros H1 H2.
    apply subcode_sss_compute_trans with (1 := H1).
    exists 1; apply sss_steps_1.
    apply in_sss_step with (l := nil).
    simpl; lia.
    constructor; auto.
  Qed.

  Fact bsm_compute_POP_0 P i x p q ll v st :
         (i,POP x p q::nil) <sc P
      -> v#>x = Zero::ll
      -> P // (p,v[ll/x]) ->> st
      -> P // (i,v) ->> st.
  Proof.
    intros H1 H2.
    apply subcode_sss_compute_trans with (1 := H1).
    exists 1; apply sss_steps_1.
    apply in_sss_step with (l := nil).
    simpl; lia.
    constructor; auto.
  Qed.

  Fact bsm_compute_POP_1 P i x p q ll v st :
         (i,POP x p q::nil) <sc P
      -> v#>x = One::ll
      -> P // (1+i,v[ll/x]) ->> st
      -> P // (i,v) ->> st.
  Proof.
    intros H1 H2.
    apply subcode_sss_compute_trans with (1 := H1).
    exists 1; apply sss_steps_1.
    apply in_sss_step with (l := nil).
    simpl; lia.
    constructor; auto.
  Qed.

  Fact bsm_compute_POP_any P i x p q b ll v st :
         (i,POP x p q::nil) <sc P
      -> v#>x = b::ll
      -> p = 1+i
      -> P // (1+i,v[ll/x]) ->> st
      -> P // (i,v) ->> st.
  Proof.
    destruct b; intros H1 H2 H3.
    apply bsm_compute_POP_1 with p q; auto.
    apply bsm_compute_POP_0 with q; subst; auto.
  Qed.

  Fact bsm_compute_PUSH P i x b v st :
         (i,PUSH x b::nil) <sc P
      -> P // (1+i,v[(b::v#>x)/x]) ->> st
      -> P // (i,v) ->> st.
  Proof.
    intros H1.
    apply subcode_sss_compute_trans with (1 := H1).
    exists 1; apply sss_steps_1.
    apply in_sss_step with (l := nil).
    simpl; lia.
    constructor; auto.
  Qed.

  Fact bsm_steps_POP_0_inv a P i x p q ll v st :
         (i,POP x p q::nil) <sc P
      -> v#>x = Zero::ll
      -> st <> (i,v)
      -> P // (i,v) -[a]-> st
      -> { b | b < a /\ P // (p,v[ll/x]) -[b]-> st }.
  Proof.
    intros H1 H2 H3 H4.
    apply sss_steps_inv in H4.
    destruct H4 as [ (_ & ?) | (b & H4) ]; subst.
    destruct H3; auto.
    exists b.
    destruct H4 as (st2 & ? & H4 & H5); subst.
    split.
    lia.
    apply sss_step_subcode_inv with (1 := H1) in H4.
    inversion H4; subst; try mydiscr; myinj.
  Qed.

  Fact bsm_steps_POP_1_inv a P i x p q ll v st :
         (i,POP x p q::nil) <sc P
      -> v#>x = One::ll
      -> st <> (i,v)
      -> P // (i,v) -[a]-> st
      -> { b | b < a /\ P // (1+i,v[ll/x]) -[b]-> st }.
  Proof.
    intros H1 H2 H3 H4.
    apply sss_steps_inv in H4.
    destruct H4 as [ (_ & ?) | (b & H4) ]; subst.
    destruct H3; auto.
    exists b.
    destruct H4 as (st2 & ? & H4 & H5); subst.
    split.
    lia.
    apply sss_step_subcode_inv with (1 := H1) in H4.
    inversion H4; subst; try mydiscr; myinj.
  Qed.

  Fact bsm_steps_POP_any_inv a P i x p q b ll v st :
         (i,POP x p q::nil) <sc P
      -> v#>x = b::ll
      -> p = 1+i
      -> st <> (i,v)
      -> P // (i,v) -[a]-> st
      -> { b | b < a /\ P // (1+i,v[ll/x]) -[b]-> st }.
  Proof.
    intros.
    destruct b.
    apply bsm_steps_POP_1_inv with p q; auto.
    apply bsm_steps_POP_0_inv with i q; subst; auto.
  Qed.

  Fact bsm_steps_POP_E_inv a P i x p q v st :
         (i,POP x p q::nil) <sc P
      -> v#>x = nil
      -> st <> (i,v)
      -> P // (i,v) -[a]-> st
      -> { b | b < a /\ P // (q,v) -[b]-> st }.
  Proof.
    intros H1 H2 H3 H4.
    apply sss_steps_inv in H4.
    destruct H4 as [ (? & ?) | (b & H4) ]; subst; auto.
    destruct H3; auto.
    exists b.
    destruct H4 as (st2 & ? & H4 & H5); subst.
    split.
    lia.
    apply sss_step_subcode_inv with (1 := H1) in H4.
    inversion H4; subst; try mydiscr; myinj.
  Qed.

  Fact bsm_steps_PUSH_inv k P i x b v st :
         (i,PUSH x b::nil) <sc P
      -> st <> (i,v)
      -> P // (i,v) -[k]-> st
      -> { a | a < k /\ P // (1+i,v[(b::v#>x)/x]) -[a]-> st }.
  Proof.
    intros H1 H2 H4.
    apply sss_steps_inv in H4.
    destruct H4 as [ (? & ?) | (a & H4) ]; subst; auto.
    destruct H2; auto.
    exists a.
    destruct H4 as (st2 & ? & H4 & H5); subst.
    split.
    lia.
    apply sss_step_subcode_inv with (1 := H1) in H4.
    inversion H4; subst; auto.
  Qed.

End Binary_Stack_Machine.

Tactic Notation "bsm" "sss" "POP" "empty" "with" uconstr(a) constr(b) constr(c) := 
     apply bsm_compute_POP_E with (x := a) (p := b) (q := c); auto.

Tactic Notation "bsm" "sss" "POP" "zero" "with" uconstr(a) constr(b) constr(c) uconstr(d) := 
     apply bsm_compute_POP_0 with (x := a) (p := b) (q := c) (ll := d); auto.

Tactic Notation "bsm" "sss" "POP" "one" "with" uconstr(a) constr(b) constr(c) uconstr(d) := 
     apply bsm_compute_POP_1 with (x := a) (p := b) (q := c) (ll := d); auto.

Tactic Notation "bsm" "sss" "POP" "any" "with" uconstr(a) constr(c) constr(d) constr(e) constr(f) := 
     apply bsm_compute_POP_any with (x := a) (p := c) (q := d) (b := e) (ll := f); auto.

Tactic Notation "bsm" "sss" "PUSH" "with" uconstr(a) constr(q) := 
     apply bsm_compute_PUSH with (x := a) (b := q); auto.

Tactic Notation "bsm" "sss" "stop" := exists 0; apply sss_steps_0; auto.

Tactic Notation "bsm" "inv" "POP" "empty" "with" hyp(H) constr(a) constr(b) constr(c) :=
     apply bsm_steps_POP_E_inv with (x := a) (p := b) (q := c) in H; auto.

Tactic Notation "bsm" "inv" "POP" "zero" "with" hyp(H) constr(a) constr(b) constr(c) constr(d) :=
     apply bsm_steps_POP_0_inv with (x := a) (p := b) (q := c) (ll := d) in H; auto.

Tactic Notation "bsm" "inv" "POP" "one" "with" hyp(H) constr(a) constr(b) constr(c) constr(d) :=
     apply bsm_steps_POP_1_inv with (x := a) (p := b) (q := c) (ll := d) in H; auto.

Tactic Notation "bsm" "inv" "POP" "any" "with" hyp(H) constr(a) constr(c) constr(d) constr(e) constr(f) :=
     apply bsm_steps_POP_any_inv with (x := a) (p := c) (q := d) (b := e) (ll := f) in H; auto.

Tactic Notation "bsm" "inv" "PUSH" "with" hyp(H) constr(a) constr(c) :=
     apply bsm_steps_PUSH_inv with (x := a) (b := c) in H; auto.

#[export] Hint Immediate bsm_sss_fun : core.
