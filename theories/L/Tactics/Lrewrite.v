From Undecidability.L Require Import Tactics.Computable Lproc Lbeta ComputableTime mixedTactics.

(** *** Lrewrite: simplification with correctness statements*)

(** This module simplifies L-terms by rewriting with correctness-lemmatas form the hint library Lrewrite *)

(* For Time Complexity: *)

Lemma redLe_app_helper s s' t t' u i j k:
  s >(<= i) s' -> t >(<= j) t' -> s' t' >(<=k) u -> s t >(<=i+j+k) u.
Proof.
  intros (i' & ? & R1)  (j' & ? & R2)  (k' & ? & R3).
  exists ((i'+j')+k'). split. omega. apply pow_trans with (t:=s' t').
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
  match goal with
    |- ?R ?s _ => is_ground s;solve [eauto 20 with Lrewrite nocore|eassumption]
  end.

Hint Extern 0 (proc _) => solve [Lproc] : Lrewrite.
Hint Extern 0 (lambda _) => solve [Lproc] : Lrewrite.
Hint Extern 0 (closed _) => solve [Lproc] : Lrewrite.

Hint Extern 0 (_ >(<= _ ) _) => eapply pow_redLe_subrelation : Lrewrite.
Hint Extern 0 (_ >* _) => eapply redLe_star_subrelation : Lrewrite.
Hint Extern 0 (_ >* _) => eapply eval_star_subrelation : Lrewrite.

(* replace int by intT if possible*)

Ltac Ltransitivity :=
  lazymatch goal with
  | |- _ >(<= _ ) _ => eapply redLe_trans
  | |- _ >* _ => eapply star_trans
  | |- _ >(_) _ => eapply pow_add with (R:=step)
  | |- ?t => fail "not supported by Ltransitivity:" t
  end.

(* generate all goals for bottom-up-rewriting*)
Ltac Lrewrite_generateGoals :=
  lazymatch goal with
  | |- app _ _ >(<= _ ) _ => eapply redLe_app_helper;[instantiate;Lrewrite_generateGoals..|idtac]
  | |- app _ _ >* _ => eapply pow_app_helper  ;[instantiate;Lrewrite_generateGoals..|idtac]
  | |- ?s >(<= _ ) _ => (is_evar s;fail 10000) ||idtac
  | |- ?s >* _ => (is_evar s;reflexivity) ||idtac
  end.

Ltac useFixHypo :=
  lazymatch goal with
    |- ?s >* ?t =>
    is_ground s;
    let IH := fresh "IH" in
    unshelve epose (IH:=_);[|(notypeclasses refine (_:{v:term & computesExp _ _ s v}));solve [eauto]|];
    let v := constr:(projT1 IH) in
    assert (IHR := fst (projT2 IH));
    let IHInts := constr:( snd (projT2 IH)) in
    lazymatch type of IHInts with
      computes ?ty _ ?v =>
      change v with (@ext _ ty _ (Build_computable IHInts)) in IHR;exact (proj1 IHR)
    end
  | |- ?s >(<= ?i ) ?t=>
    is_ground s;
    let IH := fresh "IH" in
    unshelve epose (IH:=_);[|(notypeclasses refine (_:{v:term & computesTimeExp _ _ s _ v _}));solve [eauto]|];
    let v := constr:(projT1 IH) in
    assert (IHR := fst (projT2 IH));
    let IHInts := constr:( snd (projT2 IH)) in
    lazymatch type of IHInts with
      computesTime ?ty _ ?v _=>
      change v with (@extT _ ty _ _ (Build_computableTime IHInts)) in IHR;exact (proj1 IHR)
    end
  end.

Ltac LrewriteTime_solveGoals :=
  try find_Lrewrite_lemma;
  try useFixHypo;
  lazymatch goal with
    (* Computability: *)
  | |- @ext _ (@TyB _ _)  _ ?inted >* _ =>
    (progress rewrite (ext_is_enc);[>LrewriteTime_solveGoals..]) || Lreflexivity
  | |- app (@ext _ (_ ~> _ ) _ _) (ext _) >* _ => etransitivity;[apply extApp|LrewriteTime_solveGoals]
  | |- app (@ext _ (_ ~> _ ) _ ?ints) (@enc _ ?reg ?x) >* ?v =>
    change (app (@ext _ _ _ ints) (@ext _ _ _ (reg_is_ext reg x)) >* v);LrewriteTime_solveGoals

                                                                          


  (* Complexity*)
  | |- @extT _ (@TyB _ _) _ _ ?inted >(<= _ ) _ =>
    (progress rewrite (extT_is_enc);[>LrewriteTime_solveGoals..]) || Lreflexivity
  | |- app (@extT _ (_ ~> _ ) _ _ ?fInts) (@extT _ _ _ _ ?xInts) >(<= _ ) _ => eapply redLe_trans;
    [let R := fresh "R" in
     specialize (extTApp fInts xInts) as R;
     lazymatch type of R with
       (* As we might build n using the projection on an on-ty-fly constructed computableTime-instance, we mustavoid it to depend on the proof that the time function is correct*)
       ?s >(<= ?n) ?t => let n' := eval unfold evalTime in n in
                          change (s >(<= n') t) in R
     end; exact R
    |LrewriteTime_solveGoals] 
  | |- app (@extT _ (_ ~> _ ) _ _ ?ints) (@enc _ ?reg ?x) >(<= ?k ) ?v =>
    change (app (@extT _ _ _ _ ints) (@extT _ _ _ _ (reg_is_extT reg x)) >(<= k) v);LrewriteTime_solveGoals

  (*| xInts : computes ?ty ?x ?xInt _
    |- ?R ?xInt ?res => change (R (@ext _ _ x (Build_computable xInts)) res)
                      ;reflexivity*)
  (* Correctness Lemmatas: *) 

(* do nothing to debug: use idtac here!*)
  | |- _ >(<= _ ) _ => Lreflexivity (* TO DEBUG: use idtac here*)
  | |- _ >* _ => reflexivity (* TO DEBUG: use idtac here*)
  end.

Ltac Lrewrite_old tt:=
  lazymatch goal with
    |- ?rel ?s _ =>
    lazymatch goal with             
    | |- _ >(<=_) _ =>
      try (eapply redLe_trans;[Lrewrite_generateGoals;[>LrewriteTime_solveGoals..]|])
    | |- _ >* _ =>
      try (etransitivity;[Lrewrite_generateGoals;[>LrewriteTime_solveGoals..]|])
    end;
      lazymatch goal with
        |- ?rel s _ => fail "No Progress (progress in indices are not currently noticed...)"
      (* don;t change evars if you did not make progress!*)
      | |- _ => idtac
      end
  | |- _ => idtac
  end.

Ltac Lrewrite_wrapper k:=
  lazymatch goal with
  | |- _ >(<= _) _ => k idtac
  | |- _ ⇓(<= _) _ => try (eapply evalLe_trans;[progress (Lrewrite_wrapper k);Lreflexivity|])
  | |- _ ⇓( _) _ => idtac "Lrewrite_prepare does not support s ⇓(k) y, only s ⇓(<=k) t)" (*try (eapply evalIn_trans;[progress Lrewrite_prepare;Lreflexivity|])*)
  | |- _ >(_) _ => idtac "Lrewrite_prepare does not support s >(k) y, only s >(<=k) t)"
  | |- _ >* _ => k idtac(* Lrewrite_prepare_old *)
  | |- eval _ _ => try (eapply eval_helper;[progress (Lrewrite_wrapper k);Lreflexivity|])
  | |- _ == _ => try (progress (eapply Lrewrite_equiv_helper;[try (Lrewrite_wrapper k);reflexivity..|]))
  end.

Ltac Lrewrite := Lrewrite_wrapper Lrewrite_old.


Lemma Lrewrite_in_helper s t s' t' :
  s >* s' -> t >* t' -> s == t -> s' == t'.
Proof.
  intros R1 R2 E. now rewrite R1,R2 in E.
Qed.


Tactic Notation "Lrewrite" "in" hyp(_H) :=
  lazymatch type of _H with
    | _ == _ => eapply Lrewrite_in_helper in _H; [ |try Lrewrite;reflexivity |try Lrewrite;reflexivity]
    | _ >* _ => idtac "not supported yet"
  end.

  Lemma ext_rel_helper X `(H:registered X) (x:X) (inst : computable x) (R: term -> term -> Prop) u:
    R (enc x) u -> R (@ext _ _ _ inst) u.
  Proof.
    now rewrite ext_is_enc.
  Qed.

  Lemma extT_rel_helper X `(H:registered X) (x:X) xT (inst : computableTime x xT) (R: term -> term -> Prop) u:
    R (enc x) u -> R (@extT _ _ _ _ inst) u.
  Proof.
    now rewrite extT_is_enc.
  Qed.
    

(* version of Lrewrite that the verification of the extraction uses*)
Ltac Lrewrite_new' :=
  lazymatch goal with
    |- ?R ?s _  => is_ground s
  end;
  lazymatch goal with
  | |- ?R (L.app _ _) _ =>
    (* first reduce recursively *)
    (lazymatch R with
     |  star step => refine (pow_app_helper _ _ _)
     | redLe _ => refine (redLe_app_helper _ _ _)
     end);[Lrewrite_new'..| ];

    (* then reduce here/above *)
    once match goal with
         (* beta-reduce here & recurse down again (if argument abstraction)*)
         | |- ?R (L.app (lam _) ?t) _ =>                      
           let valt := fresh "valt" in
           assert (valt:proc t) by Lproc;
           Lbeta;
           lazymatch goal with
             |- ?R (L.app (lam _) t) _ => fail "could not reduce"
           | |- _ => idtac
           end;
           clear valt;Lrewrite_new'
         | |- _ =>

           let appTimeHelper tt:=
               (lazymatch goal with
                | |- app (@extT _ (_ ~> _ ) _ _ ?fInts) (@extT _ _ _ _ ?xInts) >(<= _ ) _
                  => let R := fresh "R" in
                    specialize (extTApp fInts xInts) as R;
                    lazymatch type of R with
                      (* As we might build n using the projection on an on-ty-fly constructed computableTime-instance, we mustavoid it to depend on the proof that the time function is correct*)
                      ?s >(<= ?n) ?t => (
                        let n' := eval unfold evalTime in n in
                            change (s >(<= n') t) in R)
                    end; Ltransitivity;[exact R|]
                end) in

           (* use correctness lemmates of int here*)
           lazymatch goal with                
           | |- L.app (@ext _ (_ ~> _ ) _ _) (ext _) >* _ => Ltransitivity;[apply extApp|]
           | |- L.app (@ext _ (_ ~> _ ) _ ?ints) (@enc _ ?reg ?x) >* ?v =>
             change (app (@ext _ _ _ ints) (@ext _ _ _ (reg_is_ext reg x)) >* v);
             Ltransitivity;[apply extApp|]

           | |- L.app (@extT _ (_ ~> _ ) _ _ ?fInts) (@extT _ _ _ _ ?xInts) >(<= _ ) _ => appTimeHelper tt
           | |- L.app (@extT _ (_ ~> _ ) _ _ ?ints) (@enc _ ?reg ?x) >(<= ?k ) ?v =>
             change (L.app (@extT _ _ _ _ ints) (@extT _ _ _ _ (reg_is_extT reg x)) >(<= k) v);appTimeHelper tt                                                            
           | |- _ => idtac

           end
         end
  | |- _ => idtac
  end;
  repeat (Ltransitivity;[find_Lrewrite_lemma|Ltransitivity;[Lrewrite_new' |]]);
  try (once (Ltransitivity;[useFixHypo|]));
  (* clean up goal*)
  lazymatch goal with
  | |- ?R (@ext _ (@TyB _ ?reg) _ _) _ => eapply ext_rel_helper
  | |- ?R (@extT _ (@TyB _ ?reg) _ _ _) _ => eapply extT_rel_helper                  
  | |- _ => idtac
  end;
  (Lreflexivity).

Ltac Lrewrite_new :=
  Lrewrite_wrapper ltac:(fun _ => Lrewrite_new').

