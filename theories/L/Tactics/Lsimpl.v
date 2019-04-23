From Undecidability.L Require Export L.
From Undecidability.L.Tactics Require Import Lproc Lbeta Lrewrite Reflection mixedTactics.
Require Import ListTactics.

Local Ltac wLsimpl' _n := intros;try reflexivity';try standardizeGoal _n ; try reflexivity'.
Local Ltac wLsimpl := wLsimpl' 100.

(* Lsimpl' uses correctnes lemmas and wLsimpl*)
Ltac Lsimpl' :=
  match goal with
  | |- eval ?s _ => assert (lambda s) by Lproc;split;[ (exact (starR _ _);fail 1)|Lproc]
  | |- eval ?s _ => (progress (eapply eval_helper;[Lsimpl';reflexivity|]))

  | _ => try Lrewrite;try wLsimpl' 100
  end.

Ltac Lreduce :=
  repeat progress (try Lrewrite;try Lbeta). 
           

(*Lsimpl that uses correctnes lemmas*)
Ltac Lsimpl :=intros(*;repeat foldLocalInts*);
  lazymatch goal with
  | |- _ >(<= _ ) _ => Lreduce;try Lreflexivity
  | |- _ ⇓(_ ) _ => repeat progress Lbeta;try Lreflexivity
  | |- _ ⇓(<= _ ) _ => Lreduce;try Lreflexivity
  | |- _ >(_) _ => repeat progress Lbeta;try Lreflexivity
  | |- _ >* _ => Lreduce;try Lreflexivity (* test *)
  | |- eval _ _ => Lreduce;try Lreflexivity (* test *) 
  (*| |- _ >* _  => repeat Lsimpl';try reflexivity'
  | |- eval _ _  => repeat Lsimpl';try reflexivity'*)
  | |- _ == _  => repeat Lsimpl';try reflexivity'
  end.

Ltac LsimplHypo := standardizeHypo 100.



Tactic Notation "closedRewrite" :=
  match goal with
    | [ |- context[subst ?s _ _] ] =>
      let cl := fresh "cl" in assert (cl:closed s);[Lproc|rewrite !cl;clear cl]
                                                     
  end.

Tactic Notation "closedRewrite" "in" hyp(h):=
  match type of h with
    | context[subst ?s _ _] =>
      let cl := fresh "cl" in assert (cl:closed s);[Lproc|rewrite !cl in h;clear cl]
  end.

Tactic Notation "redStep" "at" integer(pos) := rewrite step_Lproc at pos;[simpl;try closedRewrite|Lproc].

Tactic Notation "redStep" "in" hyp(h) "at" integer(pos) := rewrite step_Lproc in h at pos;[simpl in h;try closedRewrite in h|Lproc].
(*
Tactic Notation "redStep" := redStep at 1.
*)
Tactic Notation "redStep" "in" hyp(h) := redStep in h at 1.

(* register needed lemmas:*)

Lemma rho_correct s t : proc s -> lambda t -> rho s t >* s (rho s) t.
Proof.
  intros. unfold rho,r. redStep at 1. apply star_trans_l. Lsimpl. 
Qed.

Lemma rho_correctPow s t : proc s -> lambda t -> rho s t >(3) s (rho s) t.
Proof.
  intros. unfold rho,r. change 3 with (1+2). apply pow_add.
  eexists;split. apply (rcomp_1 step). now inv H0.
  cbn. closedRewrite. apply pow_step_congL;[|reflexivity]. now Lbeta.  
Qed.

Hint Resolve rho_correct : Lrewrite.


Lemma rho_inj s t: rho s = rho t -> s = t.
Proof.
  unfold rho,r. congruence.
Qed.


Hint Resolve rho_lambda rho_cls : LProc.

Tactic Notation "recStep" constr(P) "at" integer(i):=
  match eval lazy [P] in P with
      | rho ?rP => unfold P;rewrite rho_correct at i;[|Lproc..];fold P;try unfold rP
  end.

Tactic Notation "recStep" constr(P) :=
  intros;recStep P at 1.

(*
Lemma rClosed_closed s: recProc s -> proc s.
  intros [? [? ?]]. subst. split; auto with LProc.
Qed.

Hint Resolve rClosed_closed : LProc cbv.
 *)

Lemma I_proc : proc I.
  fLproc.
Qed.

Lemma K_proc : proc K.
  fLproc.
Qed.

Lemma omega_proc : proc omega.
  fLproc.
Qed.

Lemma Omega_closed : closed Omega.
  fLproc. 
Qed.

Hint Resolve I_proc K_proc omega_proc Omega_closed: LProc.

Hint Extern 0 (I >(_) _)=> unfold I;reflexivity : Lrewrite.
Hint Extern 0 (K >(_) _)=> unfold K;reflexivity : Lrewrite.


