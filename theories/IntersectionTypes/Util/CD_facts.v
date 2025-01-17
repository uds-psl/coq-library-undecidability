Require Import Undecidability.IntersectionTypes.CD.
Require Undecidability.L.L.
From Stdlib Require Import PeanoNat List Relations Lia.
Require Import Undecidability.LambdaCalculus.Lambda.
Require Import Undecidability.LambdaCalculus.Util.term_facts.

Import L (term, var, app, lam).

From Stdlib Require Import ssreflect.

Set Default Goal Selector "!".

Unset Implicit Arguments.

#[local] Notation steps := (clos_refl_trans term step).

Lemma nth_error_seq start len n : n < len -> nth_error (seq start len) n = Some (start+n).
Proof.
  elim: len start n. { lia. }
  move=> len IH start [|n] ?. { congr Some. lia. }
  rewrite /= IH; [|congr Some]; lia.
Qed.

Inductive type_assignment_var_spec (Gamma : list ty) x t : Prop :=
  | type_assignment_var_spec_intro s phi : 
      nth_error Gamma x = Some (s, phi) -> s = t \/ In t phi -> type_assignment_var_spec Gamma x t.

Inductive type_assignment_app_spec (Gamma : list ty) M N t : Prop :=
  | type_assignment_app_spec_intro s phi : 
      type_assignment Gamma M (arr s phi t) -> type_assignment Gamma N s -> Forall (type_assignment Gamma N) phi -> type_assignment_app_spec Gamma M N t.

Lemma type_assignmentE Gamma M t : type_assignment Gamma M t ->
  match M with
  | var x => type_assignment_var_spec Gamma x t
  | lam M' => 
    match t with
    | atom _ => False
    | arr s' phi' t' => type_assignment ((s', phi') :: Gamma) M' t'
    end
  | app M' N' => type_assignment_app_spec Gamma M' N' t
  end.
Proof. by case=> * //; econstructor; eassumption. Qed.

Fixpoint sty_size (t : sty) :=
  match t with
  | atom a => 1
  | arr s phi t => 1 + sty_size s + list_sum (map sty_size phi) + sty_size t
  end.

Lemma sty_ind' (P : sty -> Prop) :
  (forall x, P (atom x)) ->
  (forall s phi t, P s -> Forall P phi -> P t -> P (arr s phi t)) ->
  forall s, P s.
Proof.
  move=> IH1 IH2. elim /(Nat.measure_induction _ sty_size). case.
  - move=> *. apply: IH1.
  - move=> s phi t IH'. apply: IH2.
    + apply: IH'=> /=. lia.
    + elim: phi IH'; first done.
      move=> s' phi' IH1' IH2'. constructor.
      * apply: IH2'=> /=. lia.
      * apply: IH1'=> /= *. apply: IH2'=> /=. lia.
    + apply: IH'=> /=. lia.
Qed.

Lemma type_assignment_fv Gamma Delta t M :
  type_assignment Gamma M t ->
  allfv (fun x => forall s phi, nth_error Gamma x = Some (s, phi) -> nth_error Delta x = Some (s, phi)) M ->
  type_assignment Delta M t.
Proof.
  elim: M Gamma Delta t.
  - move=> > /type_assignmentE [>] /= ++ IH.
    move=> /IH ??. by econstructor; eassumption.
  - move=> > IH1 > IH2 > /type_assignmentE [>].
    move=> /IH1 {}IH1 ? Hphi /= [] /IH1 ? /IH2 {}IH2 /=.
    econstructor.
    + eassumption.
    + by apply: IH2.
    + by apply: Forall_impl Hphi => ? /IH2.
  - move=> > IH ?? [] > /type_assignmentE; first done.
    move=> /IH {}IH /= H'. constructor. apply: IH.
    apply: allfv_impl H'.
    by case.
Qed.

Lemma type_assignment_ren_fv Gamma Delta xi t M :
  type_assignment Gamma M t ->
  allfv (fun x => forall s phi, nth_error Gamma x = Some (s, phi) -> nth_error Delta (xi x) = Some (s, phi)) M ->
  type_assignment Delta (ren xi M) t.
Proof.
  elim: M Gamma Delta xi t.
  - move=> > /type_assignmentE [>] /= ++ IH.
    move=> /IH ??. by econstructor; eassumption.
  - move=> > IH1 > IH2 > /type_assignmentE [>].
    move=> /IH1 {}IH1 ? Hphi /= [] /IH1 ? /IH2 {}IH2 /=.
    econstructor.
    + eassumption.
    + by apply: IH2.
    + by apply: Forall_impl Hphi => ? /IH2.
  - move=> > IH ??? [] > /type_assignmentE; first done.
    move=> /IH {}IH /= H'. constructor. apply: IH.
    apply: allfv_impl H'.
    by case.
Qed.

Lemma type_assignment_ren Gamma Delta xi t M :
  type_assignment Gamma M t ->
  (forall x s phi, nth_error Gamma x = Some (s, phi) -> nth_error Delta (xi x) = Some (s, phi)) ->
  type_assignment Delta (ren xi M) t.
Proof.
  elim: M Gamma Delta xi t.
  - move=> > /type_assignmentE [>] /= ++ IH.
    move=> /IH ??. by econstructor; eassumption.
  - move=> > IH1 > IH2 > /type_assignmentE [>].
    move=> /IH1 {}IH1 ? Hphi /[dup] /IH1 ? /IH2 {}IH2 /=.
    econstructor.
    + eassumption.
    + by apply: IH2.
    + by apply: Forall_impl Hphi => ? /IH2.
  - move=> > IH ??? [] > /type_assignmentE; first done.
    move=> /IH {}IH H' /=. constructor. apply: IH.
    by case.
Qed.

Lemma type_assignment_subst Gamma Delta sigma t M :
  type_assignment Gamma M t ->
  (forall x s phi, nth_error Gamma x = Some (s, phi) -> Forall (type_assignment Delta (sigma x)) (s::phi)) ->
  type_assignment Delta (subst sigma M) t.
Proof.
  elim: M Gamma Delta sigma t.
  - move=> > /type_assignmentE [>] /= ++ IH.
    move=> /IH /Forall_cons_iff [IH1 /Forall_forall IH2].
    by move=> [<-|/IH2].
  - move=> > IH1 > IH2 > /type_assignmentE [>].
    move=> /IH1 {}IH1 ? Hphi /[dup] /IH1 ? /IH2 {}IH2 /=.
    econstructor.
    + eassumption.
    + by apply: IH2.
    + by apply: Forall_impl Hphi => ? /IH2.
  - move=> > IH ??? [] > /type_assignmentE; first done.
    move=> /IH {}IH H' /=. constructor. apply: IH.
    move=> [|x] > /=.
    + move=> [<- <-]. apply /Forall_forall=> ??. by econstructor.
    + move=> /H'. apply: Forall_impl=> ? /type_assignment_ren. by apply.
Qed.

Lemma type_assignment_weaken Gamma Delta M t :
  (forall n t s phi, nth_error Gamma n = Some (s, phi) -> In t (s :: phi) ->
    exists s' phi', nth_error Delta n = Some (s', phi') /\ In t (s' :: phi')) ->
  type_assignment Gamma M t -> type_assignment Delta M t.
Proof.
  elim: M Gamma Delta t.
  - move=> > H /type_assignmentE [] > /H /[apply] - [?] [?] [??].
    by econstructor; eassumption.
  - move=> ? IH1 ? IH2 > H /type_assignmentE [] >.
    move: (H) => /IH1 /[apply] ?.
    move: (H) => /IH2 /[apply] ? H'.
    econstructor; [eassumption..|].
    apply: Forall_impl H' => ? /IH2. by apply.
  - move=> ? IH ?? [|??] > H /type_assignmentE; [done|].
    move=> /IH {}IH. constructor. apply: IH.
    move=> [|?] >; [|by apply: H].
    move=> /= [] *. subst. by do 3 econstructor.
Qed.

Lemma type_assignment_weaken_assumption s phi s' phi' Gamma1 Gamma2 M t :
  incl (s :: phi) (s' :: phi') ->
  type_assignment (Gamma1 ++ (s, phi) :: Gamma2) M t ->
  type_assignment (Gamma1 ++ (s', phi') :: Gamma2) M t.
Proof.
  move=> H. apply: type_assignment_weaken.
  elim: Gamma1.
  - move=> [|?] /= >.
    + move=> [<- <-] /H ?. by do 2 eexists.
    + by eauto.
  - move=> [??] > IH [|?] > /=.
    + move=> [<- <-] ?. by do 2 eexists.
    + by eauto.
Qed.

Lemma type_preservation_step {Gamma t M N} : step M N -> type_assignment Gamma M t -> type_assignment Gamma N t.
Proof.
  move=> H. elim: H Gamma t.
  - move=> > /type_assignmentE [>] /type_assignmentE *.
    apply: type_assignment_subst; [eassumption|].
    move=> [|x].
    + move=> ?? [<- <-]. by constructor.
    + move=> ?? /= Hx. apply /Forall_forall=> ? Ht.
      by econstructor; eassumption.
  - move=> > ? IH > /type_assignmentE []. by eauto using type_assignment with nocore.
  - move=> > ? IH > /type_assignmentE []. eauto using type_assignment, Forall_impl with nocore.
  - move=> > ? IH ? [] > /type_assignmentE; by eauto using type_assignment with nocore.
Qed.

Lemma type_preservation {Gamma t M N} : steps M N -> type_assignment Gamma M t -> type_assignment Gamma N t.
Proof.
  elim; by eauto using type_preservation_step with nocore.
Qed.
