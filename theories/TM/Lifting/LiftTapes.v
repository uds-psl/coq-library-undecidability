Require Import TM.Prelim TM.Relations TM.TM.

(** * Tapes-Lift *)


(** Select the [m] elements of [V], of that their index is in [I] *)
Definition select (m n: nat) (X: Type) (I : Vector.t (Fin.t n) m) (V : Vector.t X n) : Vector.t X m :=
  Vector.map (Vector.nth V) I.

Corollary select_nth m n X (I : Vector.t (Fin.t n) m) (V : Vector.t X n) (k : Fin.t m) :
  (select I V) [@ k] = V [@ (I [@ k])].
Proof. now apply Vector.nth_map. Qed.


(** Relational tapes-lift *)
Section LiftTapes_Rel.

  Variable (sig : finType) (F : Type).
  Variable m n : nat.

  Variable I : Vector.t (Fin.t n) m.

  Definition not_index (i : Fin.t n) : Prop :=
    ~ Vector.In i I.

  Variable (R : pRel sig F m).

  Definition LiftTapes_select_Rel : pRel sig F n :=
    fun t '(y, t') => R (select I t) (y, select I t').

  Definition LiftTapes_eq_Rel : pRel sig F n :=
    ignoreParam (fun t t' => forall i : Fin.t n, not_index i -> t'[@i] = t[@i]).

  Definition LiftTapes_Rel := LiftTapes_select_Rel ∩ LiftTapes_eq_Rel.

  Variable T : tRel sig m.
  
  Definition LiftTapes_T : tRel sig n :=
    fun t k => T (select I t) k.

End LiftTapes_Rel.

Arguments not_index : simpl never.
Arguments LiftTapes_select_Rel {sig F m n} I R x y /.
Arguments LiftTapes_eq_Rel {sig F m n} I x y /.
Arguments LiftTapes_Rel {sig F m n } I R x y /.
Arguments LiftTapes_T {sig m n} I T x y /.          


Lemma vector_hd_nth (X : Type) (n : nat) (xs : Vector.t X (S n)) : Vector.hd xs = xs[@Fin0].
Proof. now destruct_vector. Qed.

Lemma vector_tl_nth (X : Type) (n : nat) (i : Fin.t (S n)) (xs : Vector.t X (S (S n))) : (Vector.tl xs)[@i] = xs[@Fin.FS i].
Proof. now destruct_vector. Qed.


Section Fill.
  Variable X : Type.

  (** Replace the elements of [init] of which the index is in [I] with the element in [V] of that index. *)
  Fixpoint fill {m n : nat} (I : Vector.t (Fin.t n) m) : forall (init : Vector.t X n) (V : Vector.t X m), Vector.t X n :=
    match I with
    | Vector.nil _ => fun init V => init
    | Vector.cons _ i m' I' =>
      fun init V =>
        Vector.replace (fill I' init (Vector.tl V)) i (V[@Fin0])
    end.

  Variable m n : nat.
  Implicit Types (i : Fin.t n) (j : Fin.t m).
  Implicit Types (I : Vector.t (Fin.t n) m) (init : Vector.t X n) (V : Vector.t X m).
  
  Lemma fill_correct_nth I init V i j :
    dupfree I ->
    I[@j] = i ->
    (fill I init V)[@i] = V[@j].
  Proof.
    intros HDup Heq. revert V. induction HDup as [ | m index I' H1 H2 IH]; intros; cbn in *.
    - exfalso. clear i Heq V. now apply fin_destruct_O in j.
    - pose proof destruct_vector_cons V as (v&V'&->).
      pose proof fin_destruct_S j as [(j'&?) | ? ]; cbn in *; subst; cbn in *.
      + decide (index = I'[@j']) as [ -> | Hneq].
        * contradict H1. eapply vect_nth_In; eauto.
        * rewrite replace_nth2; auto.
      + apply replace_nth.
  Qed.

  (* Not needed *)
  (*
  Corollary select_fill I init V :
    dupfree I ->
    select I (fill I init V) = V.
  Proof. intros H. unfold select. apply Vector.eq_nth_iff. intros p ? <-. erewrite Vector.nth_map; eauto. erewrite fill_correct_nth; eauto. Qed.

  Lemma fill_select_nth I init (i : Fin.t n) :
    dupfree I ->
    (fill I init (select I init))[@i] = init[@i].
  Proof.
    intros. induction H as [ | m index I H1 H2 IH]; cbn in *.
    - reflexivity.
    - decide (index = i) as [->|d].
      + now rewrite replace_nth.
      + rewrite <- IH. now rewrite replace_nth2.
  Qed.

  Corollary fill_select I t :
    dupfree I ->
    fill I t (select I t) = t.
  Proof.
    intros H. apply Vector.eq_nth_iff. intros p ? <-. now apply fill_select_nth.
  Qed.
   *)

  Lemma fill_not_index I init V (i : Fin.t n) :
    dupfree I ->
    not_index I i ->
    (fill I init V)[@i] = init[@i].
  Proof.
    intros HDupfree. revert V i. induction HDupfree as [ | m index I' H1 H2 IH]; intros; cbn in *.
    - reflexivity.
    - pose proof destruct_vector_cons V as (v&V'&->).
      unfold not_index in *.
      decide (index = i) as [ -> | Hneq].
      + exfalso. contradict H. constructor.
      + rewrite replace_nth2; eauto. apply IH; auto.
        { intros ?. contradict H. now constructor. }
  Qed.

  Definition fill_default I (def : X) V :=
    fill I (Vector.const def n) V.

  Corollary fill_default_not_index I V def i :
    dupfree I ->
    not_index I i ->
    (fill_default I def V)[@i] = def.
  Proof. intros. unfold fill_default. rewrite fill_not_index; auto. apply Vector.const_nth. Qed.

End Fill.


Section loop_map.
  Variable A B : Type.
  Variable (f : A -> A) (h : A -> bool) (g : A -> B).
  Hypothesis step_map_comp : forall a, g (f a) = g a.

  Lemma loop_map k a1 a2 :
    loop f h a1 k = Some a2 ->
    g a2 = g a1.
  Proof.
    revert a1 a2. induction k as [ | k' IH]; intros; cbn in *.
    - destruct (h a1); now inv H.
    - destruct (h a1).
      + now inv H.
      + apply IH in H. now rewrite step_map_comp in H.
  Qed.

End loop_map.


Section LiftNM.

  Variable sig : finType.

  Variable m n : nat.

  Variable F : finType.

  Variable pM : pTM sig F m.

  Variable I : Vector.t ((Fin.t n)) m.
  Variable I_dupfree : dupfree I.

  Definition LiftTapes_trans :=
    fun '(q, sym ) =>
      let (q', act) := trans (m := projT1 pM) (q, select I sym) in
      (q', fill_default I (None, N) act).

  Definition LiftTapes_TM : mTM sig n :=
    {|
      trans := LiftTapes_trans;
      start := start (projT1 pM);
      halt := halt (m := projT1 pM);
    |}.

  Definition LiftTapes : pTM sig F n := (LiftTapes_TM; projT2 pM).

  Definition selectConf : mconfig sig (states LiftTapes_TM) n -> mconfig sig (states (projT1 pM)) m :=
    fun c => mk_mconfig (cstate c) (select I (ctapes c)).

  Lemma current_chars_select (t : tapes sig n) :
    current_chars (select I t) = select I (current_chars t).
  Proof. unfold current_chars, select. apply Vector.eq_nth_iff; intros i ? <-. now simpl_tape. Qed.

  Lemma doAct_select (t : tapes sig n) act :
    doAct_multi (select I t) act = select I (doAct_multi t (fill_default I (None, N) act)).
  Proof.
    unfold doAct_multi, select. apply Vector.eq_nth_iff; intros i ? <-. simpl_tape.
    unfold fill_default. f_equal. symmetry. now apply fill_correct_nth.
  Qed.

  Lemma LiftTapes_comp_step (c1 : mconfig sig (states (projT1 pM)) n) :
    step (M := projT1 pM) (selectConf c1) = selectConf (step (M := LiftTapes_TM) c1).
  Proof.
    unfold selectConf. unfold step; cbn.
    destruct c1 as [q t] eqn:E1.
    unfold step in *. cbn -[current_chars doAct_multi] in *.
    rewrite current_chars_select.
    destruct (trans (q, select I (current_chars t))) as (q', act) eqn:E; cbn.
    f_equal. apply doAct_select.
  Qed.

  Lemma LiftTapes_lift (c1 c2 : mconfig sig (states LiftTapes_TM) n) (k : nat) :
    loopM (M := LiftTapes_TM) c1 k = Some c2 ->
    loopM (M := projT1 pM) (selectConf c1) k = Some (selectConf c2).
  Proof.
    intros HLoop.
    eapply loop_lift with (f := step (M := LiftTapes_TM)) (h := haltConf (M := LiftTapes_TM)).
    - cbn. auto.
    - intros ? _. now apply LiftTapes_comp_step.
    - apply HLoop.
  Qed.

  Lemma LiftTapes_comp_eq (c1 c2 : mconfig sig (states LiftTapes_TM) n) (i : Fin.t n) :
    not_index I i ->
    step (M := LiftTapes_TM) c1 = c2 ->
    (ctapes c2)[@i] = (ctapes c1)[@i].
  Proof.
    intros HI H. unfold LiftTapes_TM in *.
    destruct c1 as [state1 tapes1] eqn:E1, c2 as [state2 tapes2] eqn:E2.
    unfold step, select in *. cbn in *.
    destruct (trans (state1, select I (current_chars tapes1))) as (q, act) eqn:E3.
    inv H. erewrite Vector.nth_map2; eauto. now rewrite fill_default_not_index.
  Qed.

  Lemma LiftTapes_eq (c1 c2 : mconfig sig (states LiftTapes_TM) n) (k : nat) (i : Fin.t n) :
    not_index I i ->
    loopM (M := LiftTapes_TM) c1 k = Some c2 ->
    (ctapes c2)[@i] = (ctapes c1)[@i].
  Proof.
    intros Hi HLoop. unfold loopM in HLoop.
    eapply loop_map with (g := fun c => (ctapes c)[@i]); eauto.
    intros. now apply LiftTapes_comp_eq.
  Qed.

  Lemma LiftTapes_Realise (R : Rel (tapes sig m) (F * tapes sig m)) :
    pM ⊨ R ->
    LiftTapes ⊨ LiftTapes_Rel I R.
  Proof.
    intros H. split.
    - apply (H (select I t) k (selectConf outc)).
      now apply (@LiftTapes_lift (initc LiftTapes_TM t) outc k).
    - hnf. intros i HI. now apply (@LiftTapes_eq (initc LiftTapes_TM t) outc k i HI).
  Qed.

  Lemma LiftTapes_unlift (k : nat)
        (c1 : mconfig sig (states (LiftTapes_TM)) n)
        (c2 : mconfig sig (states (LiftTapes_TM)) m) :
    loopM (M := projT1 pM) (selectConf c1) k = Some c2 ->
    exists c2' : mconfig sig (states (LiftTapes_TM)) n,
      loopM (M := LiftTapes_TM) c1 k = Some c2' /\
      c2 = selectConf c2'.
  Proof.
    intros HLoop. unfold loopM in *. cbn in *.
    apply loop_unlift with (lift:=selectConf) (f:=step (M:=LiftTapes_TM)) (h:=haltConf (M:=LiftTapes_TM)) in HLoop as (c'&HLoop&->).
    - exists c'. split; auto.
    - auto.
    - intros ? _. apply LiftTapes_comp_step.
  Qed.

  Lemma LiftTapes_Terminates T :
    projT1 pM ↓ T ->
    projT1 LiftTapes ↓ LiftTapes_T I T.
  Proof.
    intros H initTapes k Term. hnf in *.
    specialize (H (select I initTapes) k Term) as (outc&H).
    pose proof (@LiftTapes_unlift k (initc LiftTapes_TM initTapes) outc H) as (X&X'&->). eauto.
  Qed.

  Lemma LiftTapes_RealiseIn R k :
    pM ⊨c(k) R ->
    LiftTapes ⊨c(k) LiftTapes_Rel I R.
  Proof.
    intros (H1&H2) % Realise_total. apply Realise_total. split.
    - now apply LiftTapes_Realise.
    - eapply TerminatesIn_monotone.
      + apply LiftTapes_Terminates; eauto.
      + firstorder.
  Qed.

End LiftNM.

Arguments LiftTapes : simpl never.


(* TODO: AddTapes is unused, remove it *)


(* Indexes vector for adding a fixed number [m] of additional tapes at the begin. *)
Section AddTapes.

  Variable n : nat.

  Eval simpl in Fin.L 4 (Fin1 : Fin.t 10).
  Check @Fin.L.
  Search Fin.L.
  Eval simpl in Fin.R 4 (Fin1 : Fin.t 10).
  Check @Fin.R.
  Search Fin.R.

  Lemma Fin_L_fillive (m : nat) (i1 i2 : Fin.t n) :
    Fin.L m i1 = Fin.L m i2 -> i1 = i2.
  Proof.
    induction n as [ | n' IH].
    - dependent destruct i1.
    - dependent destruct i1; dependent destruct i2; cbn in *; auto; try congruence.
      apply Fin.FS_inj in H. now apply IH in H as ->.
  Qed.

  Lemma Fin_R_fillive (m : nat) (i1 i2 : Fin.t n) :
    Fin.R m i1 = Fin.R m i2 -> i1 = i2.
  Proof.
    induction m as [ | n' IH]; cbn.
    - auto.
    - intros H % Fin.FS_inj. auto.
  Qed.


  Definition add_tapes (m : nat) : Vector.t (Fin.t (m + n)) n :=
    Vector.map (fun k => Fin.R m k) (Fin_initVect _).


  Lemma add_tapes_dupfree (m : nat) : dupfree (add_tapes m).
  Proof.
    apply dupfree_map_injective.
    - apply Fin_R_fillive.
    - apply Fin_initVect_dupfree.
  Qed.

  Lemma add_tapes_select_nth (X : Type) (m : nat) (ts : Vector.t X (m + n)) k :
    (select (add_tapes m) ts)[@k] = ts[@Fin.R m k].
  Proof.
    unfold add_tapes. unfold select. erewrite !VectorSpec.nth_map; eauto.
    cbn. now rewrite Fin_initVect_nth.
  Qed.


  Definition app_tapes (m : nat) : Vector.t (Fin.t (n + m)) n :=
    Vector.map (Fin.L _) (Fin_initVect _).

  Lemma app_tapes_dupfree (m : nat) : dupfree (app_tapes m).
  Proof.
    apply dupfree_map_injective.
    - apply Fin_L_fillive.
    - apply Fin_initVect_dupfree.
  Qed.

  Lemma app_tapes_select_nth (X : Type) (m : nat) (ts : Vector.t X (n + m)) k :
    (select (app_tapes m) ts)[@k] = ts[@Fin.L m k].
  Proof.
    unfold app_tapes. unfold select. erewrite !VectorSpec.nth_map; eauto.
    cbn. now rewrite Fin_initVect_nth.
  Qed.


End AddTapes.



(** * Tactic Support *)


Lemma smpl_dupfree_helper1 (n : nat) :
  dupfree [|Fin.F1 (n := n)|].
Proof. vector_dupfree. Qed.

Lemma smpl_dupfree_helper2 (n : nat) :
  dupfree [|Fin.FS (Fin.F1 (n := n))|].
Proof. vector_dupfree. Qed.


Ltac smpl_dupfree :=
  lazymatch goal with
  | [ |- dupfree [|Fin.F1 |] ] => apply smpl_dupfree_helper1
  | [ |- dupfree [|Fin.FS |] ] => apply smpl_dupfree_helper2
  | [ |- dupfree (add_tapes _ _)] => apply add_tapes_dupfree
  | [ |- dupfree (app_tapes _ _)] => apply app_tapes_dupfree
  | [ |- dupfree _ ] => now vector_dupfree (* fallback tactic *)
  end.


Ltac smpl_TM_LiftN :=
  lazymatch goal with
  | [ |- LiftTapes _ _ ⊨ _] =>
    apply LiftTapes_Realise; [ smpl_dupfree | ]
  | [ |- LiftTapes _ _ ⊨c(_) _] => apply LiftTapes_RealiseIn; [ smpl_dupfree | ]
  | [ |- projT1 (LiftTapes _ _) ↓ _] => apply LiftTapes_Terminates; [ smpl_dupfree | ]
  end.
Smpl Add smpl_TM_LiftN : TM_Correct.


Ltac is_num_const n :=
  lazymatch n with
  | O => idtac
  | S ?n => is_num_const n
  | _ => fail "Not a number"
  end.


(*
Section Test_Is_Num_Const.
  Variable n : nat.
  Eval cbn in ltac:(is_num_const 42).
  Fail Eval cbn in ltac:(is_num_const n).
  Fail Eval cbn in ltac:(is_num_const (S n)).
End Test_Is_Num_Const.
*)


(* This tactical executes [t 0], ..., [t (n-1)]. *)
Ltac do_n_times n t :=
  match n with
  | O => idtac
  | (S ?n') =>
    t 0;
    do_n_times n' ltac:(fun i => let next := constr:(S i) in t next)
  end.
(*
Eval cbn in ltac:(do_n_times 42 ltac:(fun a => idtac a)).
*)

(* This similiar tactical executes [t Fin0], ..., [t Fin_(n-1)]. *)
Ltac do_n_times_fin_rect n m t :=
  lazymatch n with
  | O => idtac
  | S ?n' =>
    let m' := eval simpl in (pred m) in
    let one := eval simpl in (@Fin.F1 _ : Fin.t m) in
    t one;
    do_n_times_fin_rect n' m' ltac:(fun i => let next := eval simpl in (Fin.FS i) in t next)
  end.

Ltac do_n_times_fin n t := do_n_times_fin_rect n n t.

(*
Eval cbn in ltac:(do_n_times_fin 3 ltac:(fun a => idtac a)).
Eval cbn in ltac:(do_n_times_fin 3 ltac:(fun a => let x := eval simpl in (a : Fin.t 3) in idtac x)).
*)




(* Support for [app_tapes] *)

(*
 * The tactic [simpl_not_in_add_tapes] specialises hypothesises of the form
 * [H : forall i : Fin.t _, not_index (add_tapes _ m) i -> _]
 * with [i := Fin0], ..., [i := Fin(m-1)] and proves [not_index (add_tapes _ m) i.
 *)

Ltac simpl_not_in_add_tapes_step H m' :=
  let H' := fresh "HIndex_" H in
  unshelve epose proof (H ltac:(getFin m') _) as H';
  [ hnf; unfold add_tapes, Fin_initVect; cbn [tabulate Vector.map Fin.L Fin.R]; vector_not_in
  | cbn [Fin.L Fin.R] in H'
  ].

Ltac simpl_not_in_add_tapes_loop H m :=
  do_n_times m ltac:(simpl_not_in_add_tapes_step H); clear H.

Ltac simpl_not_in_add_tapes_one :=
  lazymatch goal with
  | [ H : forall i : Fin.t _, not_index (add_tapes _ ?m) i -> _ |- _] =>
    simpl_not_in_add_tapes_loop H m; clear H
  | [ H : context [ (select (add_tapes _ ?m) _)[@_]] |- _ ] =>
    rewrite ! (add_tapes_select_nth (m := m)) in H; cbn in H
  | [ |- context [ (select (add_tapes _ ?m) _)[@_]] ] =>
    rewrite ! (add_tapes_select_nth (m := m)); cbn
  end.

Ltac simpl_not_in_add_tapes := repeat simpl_not_in_add_tapes_one.

(* Test *)
Goal True.
  assert (forall i : Fin.t 3, not_index (add_tapes _ 2) i -> i = i) by firstorder.
  simpl_not_in_add_tapes. (* :-) *)
Abort.

Goal True.
  assert (n : nat) by constructor.
  assert (forall i : Fin.t (S n), not_index (add_tapes n 1) i -> True) by firstorder.
  simpl_not_in_add_tapes.
Abort.


(* Support for [app_tapes] *)


Ltac simpl_not_in_app_tapes_step H n m' :=
  let H' := fresh "HIndex_" H in
  unshelve epose proof (H (Fin.R n ltac:(getFin m')) _) as H';
  [ hnf; unfold app_tapes, Fin_initVect; cbn [tabulate Vector.map Fin.L Fin.R]; vector_not_in
  | cbn [Fin.L Fin.R] in H'
  ].

Ltac simpl_not_in_app_tapes_loop H n m :=
  do_n_times m ltac:(fun m' => simpl_not_in_app_tapes_step H n m'); clear H.

Ltac simpl_not_in_app_tapes_one :=
  lazymatch goal with
  | [ H : forall i : Fin.t _, not_index (app_tapes ?n ?m) i -> _ |- _] =>
    simpl_not_in_app_tapes_loop H n m; clear H
  | [ H : context [ (select (app_tapes ?n ?m) _)[@_]] |- _ ] =>
    rewrite ! (app_tapes_select_nth (n := n) (m := m)) in H; cbn in H
  | [ |- context [ (select (app_tapes ?n ?m) _)[@_]] ] =>
    rewrite ! (app_tapes_select_nth (n := n) (m := m)); cbn
  end.


Ltac simpl_not_in_app_tapes := repeat simpl_not_in_app_tapes_one.

Goal True.
  assert (forall i : Fin.t 10, not_index (app_tapes 8 _) i -> i = i) as Inj by firstorder.
  simpl_not_in_app_tapes.
  Check HIndex_Inj : Fin8 = Fin8.
  Check HIndex_Inj0 : Fin9 = Fin9.
  Fail Check HInj.
Abort.



(* Check whether a vector (syntactically) contains an element *)
Ltac vector_contains a vect :=
  lazymatch vect with
  | @Vector.nil ?A => fail "Vector doesn't contain" a
  | @Vector.cons ?A a ?n ?vect' => idtac
  | @Vector.cons ?A ?b ?n ?vect' => vector_contains a vect'
  | _ => fail "No vector" vect
  end.

Fail Check ltac:(vector_contains 42 (@Vector.nil nat); idtac "yes!").
Check ltac:(vector_contains 42 [|4;8;15;16;23;42|]; idtac "yes!").

Ltac vector_doesnt_contain a vect :=
  tryif vector_contains a vect then fail "Vector DOES contain" a else idtac.


Check ltac:(vector_doesnt_contain 42 (@Vector.nil nat); idtac "yes!").
Check ltac:(vector_doesnt_contain 9 [|4;8;15;16;23;42|]; idtac "yes!").
Fail Check ltac:(vector_doesnt_contain 42 [|4;8;15;16;23;42|]; idtac "yes!").



(*
 * The tactic [simpl_not_in_vector] tries to specialise hypothesises of the form
 * [H : forall i : Fin.t n, not_index [F1; ...; Fk] i -> _]
 * with [i := Fin0], ..., [i := Fin(n-1)] to new assumptions [H_0].
 *)

Ltac simpl_not_in_vector_step H vect n m' :=
  let H' := fresh H "_" in
  tryif vector_contains m' vect
  then idtac (* skip m' *)
  else pose proof (H m' ltac:(vector_not_in)) as H'.

Ltac simpl_not_in_vector_loop H vect n :=
  let H' := fresh H "_" in
  pose proof I as H';
  do_n_times_fin n ltac:(fun m' => simpl_not_in_vector_step H vect n m');
  clear H'.

Ltac simpl_not_in_vector_one :=
  lazymatch goal with
  | [ H : forall i : Fin.t ?n, not_index ?vect i -> _ |- _ ] =>
    simpl_not_in_vector_loop H vect n; clear H
  end.

Ltac simpl_not_in_vector := repeat simpl_not_in_vector_one.


(* Test *)
Goal True.
  assert (forall i : Fin.t 10, not_index [|Fin8; Fin1; Fin2; Fin3|] i -> i = i) as HInj by firstorder.
  simpl_not_in_vector_one.
  Fail Check HInj.
  Show Proof.
  Check (HInj_0 : Fin0 = Fin0).
  Check (HInj_1 : Fin4 = Fin4).
  Check (HInj_2 : Fin5 = Fin5).
  Check (HInj_3 : Fin6 = Fin6).
  Check (HInj_4 : Fin7 = Fin7).
  Check (HInj_5 : Fin9 = Fin9).
Abort.



Ltac simpl_not_in :=
  repeat match goal with
         | _ => progress simpl_not_in_add_tapes
         | _ => progress simpl_not_in_app_tapes
         | _ => progress simpl_not_in_vector
         end.