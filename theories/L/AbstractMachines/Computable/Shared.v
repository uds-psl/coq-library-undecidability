From Undecidability.L Require Import L.
From Undecidability.L.AbstractMachines Require Import Programs FunctionalDefinitions.
From Undecidability.L.Datatypes Require Import LNat LProd Lists LOptions.
From Undecidability.L.Tactics Require Import LTactics.

(** * Computability in L *)
(** *** Encoding for Tokens *)

Run TemplateProgram (tmGenEncode "token_enc" Tok).
Hint Resolve token_enc_correct : Lrewrite.

Fixpoint jumpTarget_tr' l res P {struct P} : option (list Tok * list Tok) :=
  match P with
  | [] => None
  | lamT :: P0 => jumpTarget_tr' (S l) (lamT::res) P0
  | retT :: P0 => match l with
                | 0 => Some (rev res, P0)
                | S l0 => jumpTarget_tr' l0 (retT::res) P0
                end
  | t::P => jumpTarget_tr' l (t::res) P
  end.

Definition jumpTarget_tr l res P := jumpTarget_tr' l (rev res) P.

Lemma jumpTarget_tr_extEq : extEq  jumpTarget_tr jumpTarget.
Proof.
  intros l res P. unfold jumpTarget_tr. hnf.
  induction P as [|[]]in res,l |-*. 5:destruct l.
  all:cbn. all:try rewrite <- IHP. all:simpl_list;cbn. all:try congruence.
Qed.

Instance term_jump_target_tr' : computableTime jumpTarget_tr' (fun l _ => (5,fun res _ => (1,fun P _ => (length P * 36 +length res * 13 + 4,tt)))).
extract. solverec.
Qed.

Instance term_jump_target : computableTime jumpTarget (fun l _ => (1,fun res _ => (1,fun P _ => (length P * 36 + length res * 26+ 21,tt)))).
eapply computableTimeExt. now exact jumpTarget_tr_extEq. unfold jumpTarget_tr.
extract. solverec. rewrite rev_length. Lia.lia.
Qed.
