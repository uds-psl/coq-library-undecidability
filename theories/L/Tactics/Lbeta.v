From Undecidability.L Require Import Util.L_facts.
Require Import ListTactics.
From Undecidability.L.Tactics Require Import Lproc Reflection. 

(* *** Lbeta: symbolic beta reduction *)

(* This module procides tactics to simlify L-term w.r.t beta reduction in L.
It does so by the reflective tactic simplify_L' using the module Reflextion. *)

Lemma eval_helper s t u: s >* u -> eval u t -> eval s t.
  intros R H. now rewrite R.
Defined.

Ltac addToList a l := AddFvTail a l.

Ltac has_no_evar s := try (has_evar s;fail 1).

Ltac reflexivity' :=
  match goal with
    | |- ?G => has_no_evar G;reflexivity
  end.

Lemma evalIn_refl n s : proc s -> s ⇓(<=n) s.
Proof.
  intros. split.
  -exists 0;split.
   +lia.
   +reflexivity.
  -Lproc.
Defined.

Lemma eval_refl s : lambda s -> s ⇓ s.
Proof.
  intros. split. reflexivity. Lproc.
Defined.


(*make all variables to coq-variables in the context *)
Ltac allVarsPrep _s :=
lazymatch _s with
| var ?_n => idtac
| app ?_s ?_t =>
  allVarsPrep _s;
  allVarsPrep _t
| lam ?_s => allVarsPrep _s
| rho ?_s => allVarsPrep _s
| _ => let x := fresh "__x" in set (x:= _s)
end.

Ltac allVarsSubstL vars :=
lazymatch vars with
| [] => idtac
| ?x::?vars'' => try subst x;allVarsSubstL vars''
end.

Ltac allVars' vars _s :=
lazymatch _s with
| var ?_n => vars
| app ?_s ?_t =>
  let vars := allVars' vars _s in
  allVars' vars _t
| lam ?_s => allVars' vars _s
| rho ?_s => allVars' vars _s
| _ => addToList (_s:term) (* cast is for coersions to work *) vars
end.

Ltac allVars _s := allVars' (@nil term) _s.

Ltac Find_at' a l :=
  lazymatch l with
  | (cons a _) => constr:(0)
  | (cons _ ?l) =>
    let n := Find_at' a l in
    constr:(S n)
  end.

Ltac reifyTerm vars _s :=
  lazymatch _s with
    | var ?_n => constr:(rVar _n)
    | app ?_s ?_t =>
      let _s := reifyTerm vars _s in
      let _t := reifyTerm vars _t in
      constr:(rApp _s _t)
    | lam ?_s =>
      let _s := reifyTerm vars _s in
      constr:(rLam _s)
    | rho ?_s =>
      let _s := reifyTerm vars _s in
      constr:(rRho _s)
    | _ =>
      let vars' := eval hnf in vars in
          let _n := (Find_at' (_s:term) (* cast is for coersions to work *) vars') in
          constr:(rConst (_n))
  end.

Ltac vm_hypo :=
  match goal with
    | H: ?s == ?t |- _ => revert H;try vm_hypo;intros H; vm_compute in H
  end.

Ltac ProcPhi vars := 
  let H := fresh "H" in
  let s := fresh "s" in
  apply liftPhi_correct,Forall_forall;allVarsSubstL vars;
  repeat
    once lazymatch goal with
    | |- Forall _ (@nil _) => solve [simple apply Forall_nil]
    | |- _ => simple apply Forall_cons;[Lproc| ]
    end .

(* solve goals of shape s >(?l) ?t for evars ?l, ?t!*)
Ltac simplify_L' n:=
  once lazymatch goal with
    |- ?s >(_) _ =>
    allVarsPrep s;
    once lazymatch goal with
      |- ?s >(_) _ =>
      let vars:= allVars s in
  (*    let vars' := fresh "vars'" in
     pose (vars':=vars); *)
      let s' := reifyTerm vars s in
      let phi := fresh "phi" in
      pose (phi := Reflection.liftPhi vars);
      let pp := fresh "pp" in
      let cs := fresh "cs" in
      assert (pp:Reflection.Proc phi) by (ProcPhi vars;shelve);
      assert (cs :Reflection.rClosed phi s') by (simple apply Reflection.rClosed_decb_correct;[exact pp|vm_cast_no_check (@eq_refl bool true) ]);
      let R := fresh "R" in
      assert (R:= Reflection.rStandardizeUsePow n pp cs);
      let eq := fresh "eq" in
      let s'' := fresh "s''" in
      set (s'':= Reflection.rCompSeval n (0, Reflection.rCompClos (s') [])) in R;
      vm_compute in (value of s'');
      subst s''; lazy -[rho pow phi Reflection.liftPhi] in R;
      lazy [phi Reflection.liftPhi nth] in R;
      (*repeat allVarsSubstL vars';*)      
      clear (*vars' eq *) cs phi pp; exact  R
    end
  end.


Lemma pow_trans_eq: forall (s t u : term) (i j k: nat), s >(i) t -> t >(j) u -> i+j=k -> s >(k) u.
  intros. subst. eapply pow_trans;eauto. 
Qed.

Ltac Lreflexivity :=
  once lazymatch goal with
  | |- _ ⇓(<=_) _ => solve [apply (@evalIn_refl 0);Lproc | apply evalIn_refl;Lproc ]
  | |- _ >(<= _ ) _ => apply redLe_refl
  | |- _ ⇓(?i) _ => unify i 0;split;[reflexivity|Lproc]
  | |- _ ⇓ _ => solve [apply eval_refl;Lproc]
  | |- _ >* _ => reflexivity
  | |- _ >(_) _ => now apply pow0_refl
  | |- ?t => fail "not supported by Lreflexivity:" t
  end.


Ltac Lbeta' n :=
  once lazymatch goal with
    |- ?rel ?s _ =>    
    once lazymatch goal with
    | |- _ >(?i) _ => tryif is_evar i
      then eapply pow_trans;[simplify_L' n|]
      else (eapply pow_trans_eq;[simplify_L' n| |try reflexivity])
    | |- _ >(<=?i) _ => tryif is_evar i
      then eapply redLe_trans;[apply pow_redLe_subrelation;simplify_L' n|]
      else ((eapply redLe_trans_eq;[ | apply pow_redLe_subrelation;simplify_L' n| ]);[try reflexivity | ..])
                                             
    | |- _ ⇓(<= _) _ => eapply evalLe_trans;[apply pow_redLe_subrelation;simplify_L' n|]
    | |- _ ⇓(_) _ => eapply evalIn_trans;[Lbeta' n|]                                                  
    | |- _ ⇓ _ => eapply eval_helper;[eapply pow_star_subrelation;simplify_L' n|]
    | |- _ >* _ => etransitivity;[eapply pow_star_subrelation;simplify_L' n|]
    | |- ?G => fail "Not supported for LSimpl (or other failed):" G 
    end;
    once lazymatch goal with
      |- ?rel s _ => fail "No Progress (progress in indexes are not currently noticed...)"
    | |- _ => idtac
    (* don;t change evars if you did not make progress!*)
    end
  end.
        
Tactic Notation "Lbeta" := once(Lbeta' 50).


(* test, approx. 2+1 seconds (proof + qed) on w550s
Lemma test : (lam 0) (lam 0) >(1 ) (lam 0).
Proof.
  do 300 (assert ((lam 0) (lam 0) >(1 ) (lam 0)) by (unfold I;simplify_L' 50);clear H);
    simplify_L' 50.
Qed.*)

(* legacy: asserts R:= s >* ?t for some reduction of ?t *)
Tactic Notation "standardize" ident(R) constr(n) constr(s) :=
  has_no_evar s;
  let l := fresh "l" in
  let t := fresh "t" in
  evar (l : nat);
  evar (t : term); 
  assert (R : s >(l) t) by simplify_L' n;subst l t;apply pow_star in R.


(* Goal I I >* I. *)
(* Proof.  *)
(*   standardize R 100 ((lam 0) (lam 0)); exact R.  *)
(* Qed. *)

Ltac standardizeGoal' _n:=
  let R:= fresh "R" in
  once lazymatch goal with (* try etransitivity is for debugging, so we can disable ProcPhi iff needed*)
    | |- ?s == _ => let R:= fresh "R" in standardize R _n s;try (etransitivity;[exact (star_equiv R)|];clear R)
    | |- ?s >* _ => let R:= fresh "R" in standardize R _n s;try (etransitivity;[exact R|];clear R)
  end.

Ltac standardizeGoal _n :=
  try progress Lbeta' _n;
  try progress standardizeGoal' _n;
    try progress (symmetry;standardizeGoal' _n;symmetry).

Lemma stHypo s s' t : s >* s' -> s == t -> s' == t.
Proof.
  intros R R'. rewrite R in R'. exact R'.
Qed.

Ltac standardizeHypo _n:=
match goal with
  | eq_new_name : ?s == ?t |- _=>
    revert eq_new_name;try standardizeHypo _n; intros eq_new_name;
    try (progress (let R:= fresh "R" in
                   standardize R _n s;apply (stHypo R) in eq_new_name;clear R ));
      try (progress (let R':= fresh "R'" in
                     symmetry;standardize R' _n s;
                     apply (stHypo R') in eq_new_name;symmetry;clear R' ))
end.
