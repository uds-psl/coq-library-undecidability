From Undecidability.L Require Import Tactics.Computable Lproc Lbeta.
Import L_Notations.

(* *** Lrewrite: simplification with correctness statements*)

(* This module simplifies L-terms by rewriting with correctness-lemmatas form the hint library Lrewrite *)

(* For Time Complexity: *)

Lemma redLe_app_helper s s' t t' u i j k:
  s >(<= i) s' -> t >(<= j) t' -> s' t' >(<=k) u -> s t >(<=i+j+k) u.
Proof.
  intros (i' & ? & R1)  (j' & ? & R2)  (k' & ? & R3).
  exists ((i'+j')+k'). split. lia. apply pow_trans with (t:=s' t').
  apply pow_trans with (t:=s' t).
  now apply pow_step_congL.
  now apply pow_step_congR. eauto. 
Qed.

Lemma pow_app_helper s s' t t' u:
  s >* s' -> t >* t' -> s' t' >* u -> s t >* u.
Proof.
  now intros -> -> -> . 
Qed.


Lemma LrewriteTime_helper s s' t i :
  s' = s -> s >(<= i) t -> s' >(<= i) t.
Proof.
  intros;now subst. 
Qed.

Lemma Lrewrite_helper s s' t :
  s' = s -> s >* t -> s' >* t.
Proof.
  intros;now subst. 
Qed.

Lemma Lrewrite_equiv_helper s s' t t' :
  s >* s' -> t >* t' -> s' == t' -> s == t.
Proof.
  intros -> ->. tauto. 
Qed.


Ltac find_Lrewrite_lemma :=
  once lazymatch goal with
    | |- ?R (lam _) => fail
    | |- ?R (enc _) => fail
    | |- ?R (ext (ty:=TyB _) _) => fail
    | |- ?R ?s _ => has_no_evar s;solve [eauto 20 with Lrewrite nocore]
  end.

Create HintDb Lrewrite discriminated.
#[export] Hint Constants Opaque : Lrewrite.
#[export] Hint Variables Opaque : Lrewrite.

#[export] Hint Extern 0 (proc _) => solve [Lproc] : Lrewrite.
#[export] Hint Extern 0 (lambda _) => solve [Lproc] : Lrewrite.
#[export] Hint Extern 0 (closed _) => solve [Lproc] : Lrewrite.

Lemma pow_redLe_subrelation' i s t : pow step i s t -> redLe i s t.
Proof. apply pow_redLe_subrelation. Qed. (* for performance, without [subrelation] in type*)


#[export] Hint Extern 0 (_ >(<= _ ) _) => simple eapply pow_redLe_subrelation' : Lrewrite.
#[export] Hint Extern 0 (_ >* _) => simple eapply redLe_star_subrelation : Lrewrite.
#[export] Hint Extern 0 (_ >* _) => simple eapply eval_star_subrelation : Lrewrite.

(* replace int by intT if possible*)

Ltac Ltransitivity :=
  once lazymatch goal with
  | |- _ >(<= _ ) _ => refine (redle_trans _ _);[shelve.. | | ]
  | |- _ >* _ => refine (star_trans _ _);[shelve.. | | ]
  | |- _ >(_) _ => eapply pow_add with (R:=step)
  | |- ?t => fail "not supported by Ltransitivity:" t
  end.

(* generate all goals for bottom-up-rewriting*)
Ltac Lrewrite_generateGoals :=
  once lazymatch goal with
  | |- app _ _ >(<= _ ) _ => eapply redLe_app_helper;[idtac;Lrewrite_generateGoals..|idtac]
  | |- app _ _ >* _ => eapply pow_app_helper  ;[idtac;Lrewrite_generateGoals..|idtac]
  | |- ?s >(<= _ ) _ => (is_evar s;fail 10000) ||idtac
  | |- ?s >* _ => (is_evar s;reflexivity) ||idtac
  end.

Ltac useFixHypo :=
  once lazymatch goal with
    |- ?s >* ?t =>
    has_no_evar s;
    let IH := fresh "IH" in
    unshelve epose (IH:=_);[|(notypeclasses refine (_:{v:term & computesExp _ _ s v}));solve [once auto with nocore]|];
    let v := constr:(projT1 IH) in
    assert (IHR := fst (projT2 IH));
    let IHInts := constr:( snd (projT2 IH)) in
    once lazymatch type of IHInts with
      computes ?ty _ ?v =>
      change v with (@ext _ ty _ (Build_computable IHInts)) in IHR;exact (proj1 IHR)
    end
  end.

Ltac LrewriteTime_solveGoals :=
  try find_Lrewrite_lemma;
  try useFixHypo;
  once lazymatch goal with
    (* Computability: *)
  | |- @ext _ (@TyB _ _)  _ ?inted >* _ =>
    (progress rewrite (ext_is_enc);[>LrewriteTime_solveGoals..]) || Lreflexivity
  | |- app (@ext _ (_ ~> _ ) _ _) (ext _) >* _ => etransitivity;[apply extApp|LrewriteTime_solveGoals]
  | |- app (@ext _ (_ ~> _ ) _ ?ints) (@enc _ ?reg ?x) >* ?v =>
    change (app (@ext _ _ _ ints) (@ext _ _ _ (reg_is_ext reg x)) >* v);LrewriteTime_solveGoals
  | |- _ >* _ => reflexivity (* TO DEBUG: use idtac here*)
  end.

Ltac Lrewrite' :=
  once lazymatch goal with
    |- ?rel ?s _ =>
    once lazymatch goal with             
    | |- _ >(<=_) _ =>
      try (eapply redle_trans;[Lrewrite_generateGoals;[>LrewriteTime_solveGoals..]|])
    | |- _ >* _ =>
      try (etransitivity;[Lrewrite_generateGoals;[>LrewriteTime_solveGoals..]|])
    end;
      once lazymatch goal with
        |- ?rel s _ => fail "No Progress (progress in indices are not currently noticed...)"
      (* don;t change evars if you did not make progress!*)
      | |- _ => idtac
      end
  | |- _ => idtac
  end.

Tactic Notation "Lrewrite_wrapper" tactic(k):=
once lazymatch goal with
| |- _ >(<= _) _ => k
| |- _ >(_) _ => idtac "Lrewrite_prepare does not support s >(k) y, only s >(<=k) t)"
| |- _ >* _ => k (* Lrewrite_prepare_old *)
| |- eval _ _ => (eapply eval_helper;[k;Lreflexivity|])
| |- _ == _ => progress ((eapply Lrewrite_equiv_helper;[try (* inefficient, but needed if only one side does progress *)k;reflexivity..|]))
end.

(* does work on coq variables that are not abstactions *)
Ltac Lrewrite := Lrewrite_wrapper Lrewrite'.



Lemma Lrewrite_in_helper s t s' t' :
  s >* s' -> t >* t' -> s == t -> s' == t'.
Proof.
  intros R1 R2 E. now rewrite R1,R2 in E.
Qed.


Tactic Notation "Lrewrite" "in" hyp(_H) :=
  once lazymatch type of _H with
    | _ == _ => eapply Lrewrite_in_helper in _H; [ |try Lrewrite;reflexivity |try Lrewrite;reflexivity]
    | _ >* _ => idtac "not supported yet"
  end.

Lemma ext_rel_helper X `(H:encodable X) (x:X) (inst : computable x) (R: term -> term -> Prop) u:
  R (enc x) u -> R (@ext _ _ _ inst) u.
Proof.
  now rewrite ext_is_enc.
Qed.
 
Lemma redLe_app_helperL s s' t u i j:
s >(<= i) s' -> app s' t >(<=j) u -> app s t >(<=i+j) u.
Proof. intros ? H'. eapply redLe_app_helper in H'. 2:eassumption. 2:Lreflexivity. now rewrite Nat.add_0_r in H'. Qed. 

Lemma redLe_app_helperR s t t' u i j:
t >(<= i) t' -> app s t' >(<=j) u -> app s t >(<=i+j) u.
Proof. intros ? H'. eapply redLe_app_helper in H'. 3:eassumption. 2:Lreflexivity. eassumption. Qed.

Lemma pow_app_helperL s s' t u:
s >* s' -> app s' t >* u -> app s t >* u.
Proof. now intros -> -> . Qed.

Lemma pow_app_helperR s t t' u:
t >* t' -> app s t' >* u -> app s t >* u.
Proof. now intros -> -> . Qed.


Ltac LrewriteSimpl_appL R:=
  lazymatch R with
  | star step => refine (pow_app_helperL _ _)
  | redLe _ => refine (redLe_app_helperL _ _)
  end.

Ltac LrewriteSimpl_appR R:=
lazymatch R with
| star step => refine (pow_app_helperR _ _)
| redLe _ => refine (redLe_app_helperR _ _)
end.

Ltac isValue s:=
  lazymatch s with
  | lam _ => idtac
  | app _ _ => fail
  | @ext _ _ _ _ => idtac
  | @enc _ _ _ => idtac
  | I => idtac
  | ?P => tryif (is_var P;lazymatch eval unfold P in P with rho _ => idtac end) then idtac
          else
          lazymatch goal with
          | H : proc s |- _  => idtac
          | H : lambda s |- _ => idtac
          | _ => (* idtac "noFastValue, default to true" s; *)idtac
          end
  end.

(* version of Lrewrite that des the beta-steps as well *)
(* clears the flag iff head is not applied to values *)
Ltac LrewriteSimpl'' canReduceFlag :=
  idtac;
  (* time "LrewriteSimpl'" *) 
  once lazymatch goal with
  | |- _ (@ext _ (@TyB _ ?reg) _ _) _ => refine (ext_rel_helper _ _) (* for backwards-compability, if used on term with hole*)
  | |- ?R ?s _  => has_no_evar s;(* idtac "recurse to" s; *)

  repeat' (idtac;
    lazymatch goal with
    | |- _ (lam _) _ => fail
    | |- _ (enc _) _ => fail
      
    (* use correctness lemmatas of int here*)  
    | |- L.app (@ext _ (_ ~> _ ) _ _) (ext _) >* _ => Ltransitivity;[apply extApp|]
    | |- L.app (@ext _ (_ ~> _ ) _ ?ints) (@enc _ ?reg ?x) >* ?v =>
      change (app (@ext _ _ _ ints) (@ext _ _ _ (reg_is_ext reg x)) >* v);
      Ltransitivity;[refine (extApp _ _)|]
    (* clean up goal *)
    | |- _ (@ext _ (@TyB _ ?reg) _ _) _ => refine (ext_rel_helper _ _)

      (* last reduce recursively, and then try to apply rewrite lemmas o Lbeta *)
    | |- ?R (L.app _ _) _ =>
      (* idtac "at app0"; *)
      let progressFlag := fresh in
      let recCanReduceFlag := fresh  in
      let tmp := fresh in
      assert (progressFlag:=tt);
      assert (tmp:=tt);
      assert (recCanReduceFlag:=tt);
      try (LrewriteSimpl_appR R;[solve [LrewriteSimpl'' tmp;Lreflexivity]|(* idtac"didR"; *)try clear progressFlag]);
      try clear tmp; (*we don't care for RHS*)
      try (LrewriteSimpl_appL R;[solve [LrewriteSimpl'' canReduceFlag;Lreflexivity]|(* idtac"didL"; *)try clear progressFlag]);
      (* idtac "at app"; *)
      lazymatch goal with
      | |- ?R (L.app ?s ?t) _ =>
        (* idtac "still app" s t; *)
        let maybeBeta _ := lazymatch s with lam _ => Lbeta end in
        try (maybeBeta ();try clear progressFlag);
        tryif (tryif is_var recCanReduceFlag then isValue t else fail)
          then
            try (
              Ltransitivity;[solve [find_Lrewrite_lemma|useFixHypo]|];
              try clear progressFlag (* we did something *);

              (* We mus re-evaluate if we produce an assumption where s rewrite could apply*)
              try (clear canReduceFlag;pose (canReduceFlag:=tt))
            )
          else clear canReduceFlag
      end;
      (* fail if no progress *)
      tryif is_var progressFlag then (* lazymatch goal with |- ?H => idtac "leaving behind" H end; *)fail else idtac
(*     | |- ?H => fail 1000 "unexpected goal" H  *)  
    | |- ?H => (* idtac "fallback" H; *)Ltransitivity;[solve[find_Lrewrite_lemma]|]  
    end)
  end.

Ltac LrewriteSimpl' := let flag := fresh in assert (flag:=tt);
  (tryif Lbeta then try LrewriteSimpl'' flag else LrewriteSimpl'' flag);try clear flag.

Ltac LrewriteSimpl := Lrewrite_wrapper ltac:(idtac;LrewriteSimpl').
