(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Bool.


From Undecidability.PCP Require Import PCP Util.PCP_facts.

Set Implicit Arguments.

Section dec.

  Variable (X : Type) (eqX_dec : forall x y : X, { x = y } + { x <> y }).

  Fact is_a_head_dec (l t : list X) : { x | l = t++x } + { ~ exists x, l = t++x }.
  Proof using eqX_dec.
    revert t.
    induction l as [ | a l IHl ].
    + intros [ | t ]. 
      * left; exists nil; auto.
      * right; intros ([ | ] & ?); discriminate.
    + intros [ | b t ].
      * left; exists (a::l); auto.
      * destruct (eqX_dec a b) as [ -> | C ].
        - destruct (IHl t) as [ H | C ].
          ++ left; destruct H as (x & ->).
              exists x; auto.
          ++ right; contradict C; destruct C as (x & E).
             exists x; inversion E; subst; auto.
        - right; contradict C; destruct C as (? & E); inversion E; auto.
  Qed.
 
  Fact is_a_tail_dec (l t : list X) : { exists x, x++t = l } + { ~ exists x, x++t = l }.
  Proof using eqX_dec.
    destruct (is_a_head_dec (rev l) (rev t)) as [ H | H ].
    + left; destruct H as (x & Hx).
      exists (rev x).
      apply f_equal with (f := @rev _) in Hx.
      rewrite rev_app_distr in Hx.
      do 2 rewrite rev_involutive in Hx; auto.
    + right; contradict H.
      destruct H as (x & Hx); exists (rev x); subst.
      apply rev_app_distr.
  Qed.

End dec.

(* ** Specializations to BPCP *)

Theorem bpcp_hand_dec R (s t : list bool) : { R ⊳ s∕t } + { ~ R ⊳ s∕t }.
Proof. apply pcp_hand_dec, bool_dec. Qed.

Definition BPCP_input := list (list bool * list bool).
Definition BPCP_problem (R : BPCP_input) := exists l, R ⊳ l∕l.

Require Import Undecidability.Synthetic.Definitions.

Theorem dPCPb_to_BPCP : dPCPb ⪯ BPCP_problem.
Proof.
  exists (fun R => R). intros R. tauto.
Qed.
