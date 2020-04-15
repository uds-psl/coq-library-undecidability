From Undecidability.L Require Import ComputableTactics Lproc mixedTactics Tactics.Computable ComputableTime Lrewrite.

Import L_Notations.

Local Fixpoint subst' (s : term) (k : nat) (u : term) {struct s} : term :=
  match s with
  | # n => if Init.Nat.eqb n k then u else # n
  | app s0 t => (subst' s0 k u) (subst' t k u)
  | (lam s0) => (lam (subst' s0 (S k) u))
  end.

Lemma subst'_eq s k u: subst s k u = subst' s k u.
  revert k;induction s;intros;simpl;try congruence.
  (* dec;destruct (n =? k) eqn:eq;try reflexivity. *)
  (* -apply beq_nat_false in eq. tauto. *)
  (* -apply beq_nat_true in eq. exfalso; tauto.  *)
Qed.

Lemma lStep s t u: lambda t -> (subst' s 0 t) >* u -> (lam s) t >* u.
Proof.
  intros. rewrite <- H0. apply step_star_subrelation. rewrite <- subst'_eq. now apply step_Lproc.
Qed.


Lemma subst'_cls s : closed s -> forall x t, subst' s x t = s.
  intros. rewrite <- subst'_eq. apply H. 
Qed.

Ltac redStep':=
  match goal with
      |- _ == _ => apply star_equiv;redStep'
    | |- app (lam ?s) ?t >* _ => apply lStep;[now Lproc|reflexivity]
    | |- app ?s ?t >* _ => progress (etransitivity;[apply star_step_app_proper;redStep'|]);[reflexivity]
    | |- _ => reflexivity
  end.

Ltac redStep2 := etransitivity;[redStep'|].
(*
iLtac redSimpl' s x t:=
  match s with
    | app ?s1 ?s2 ->
      let s1' := resSimpl' s1 x t in
      let s2' := resSimpl' s2 x t in
      constr:(app s1' s2')
    | 
 *)


Ltac Lbeta_old := cbn [subst' Init.Nat.eqb].

Lemma subst'_int (X:Set) (ty : TT X) (f:X) (H : computable f) : forall x t, subst' (ext f) x t = (ext f).
  intros. apply subst'_cls. Lproc.
Qed.
(*
Lemma subst'_enc Y  (H:registered  Y): forall y x t, subst' (enc y) x t = (enc y).
  intros. apply subst'_cls. Lproc.
Qed.
*)

Local Ltac closedRewrite2 := rewrite ?subst'_int;
  match goal with
    | [ |- context[subst' ?s _ _] ] =>
      let cl := fresh "cl" in assert (cl:closed s) by Lproc;
        let cl' := fresh "cl'" in assert (cl':= subst'_cls cl);
        rewrite ?cl';clear cl;clear cl'
                              
  end.

Lemma app_eq_proper (s s' t t' :term) : s = s' -> t = t' -> s t = s' t'.
  congruence.
Qed.

Lemma lam_app_proper (s s' :term) : s = s' -> lam s = lam s'.
  congruence.
Qed.

Lemma subst'_eq_proper (s s':term) x t : s = s' -> subst' s x t = subst' s' x t.
  congruence.
Qed.

Lemma clR s s' t : s' = s -> s >* t -> s' >* t.
  congruence.
Qed.

Lemma clR' s s' t : s' = s -> s == t -> s' == t.
  congruence.
Qed.

Lemma subst'_rho s x u : subst' (rho s) x u = rho (subst' s (S x) u).
Proof.
  reflexivity.
Qed.

Ltac closedRewrite3' :=
  match goal with
    | |- app _ _ = _ => try etransitivity;[progress (apply app_eq_proper;closedRewrite3';reflexivity)|]
    | |- lam _ = _ => apply lam_app_proper;closedRewrite3'
    | |- rho _ = _ => eapply f_equal;Lbeta_old;closedRewrite3'
    | |- subst' (subst' _ _ _) _ _ = _ => etransitivity;[apply subst'_eq_proper;closedRewrite3'|closedRewrite3']
    | |- subst' (subst' _ _ _) _ _ = _ => etransitivity;[apply subst'_eq_proper;closedRewrite3'|closedRewrite3']
    | |- subst' (ext _) _ _ = _ => apply subst'_int
    | |- subst' (rho _) _ _ = _ => rewrite subst'_rho;f_equal;closedRewrite3'
    | |- subst' _ _ _ = _ => apply subst'_cls;now Lproc
    | |- _ => reflexivity
  end.

Ltac closedRewrite3 := etransitivity;[cbn;(eapply clR||eapply clR');closedRewrite3';reflexivity|].


Ltac Lred' := (progress redStep2); Lbeta_old.
Tactic Notation "redStep" := Lred';closedRewrite3.

Ltac redSteps := progress (reflexivity || ((repeat Lred');closedRewrite3)).

Ltac LsimplRed := repeat ( redSteps ; try Lrewrite).
