From Undecidability.L Require Import L.

Notation "A '.[' i  ']'" := (elAt A i) (no associativity, at level 50).

Fixpoint appCross A B :=
match A with
| nil => nil
| a :: A => map (app a) B ++ appCross A B 
end.

Fixpoint T n := 
match n with
| 0 => [#n]
| S n => let A := T n in A ++ [#(S n)] ++ filter (fun x => Dec (~ x el A)) ( map lam A ++ appCross A A )
end.

Lemma sublist_T : forall n : nat, exists (x : term) (B : list term), T (S n) = T n ++ x :: B.
Proof.
  intros n. exists (# (S n)). simpl. eexists; reflexivity.
Qed.

Lemma T_S s n m : T n .[ m ] = Some s -> T (S n).[ m ] = Some s.
Proof.
  destruct (sublist_T n) as [x [B H]]. rewrite H. eapply elAt_app.
Qed.

Lemma T_ge s n1 n2 m : n2 >= n1 -> T n1 .[ m ] = Some s -> T n2 .[ m ] = Some s.
Proof.
  remember (S n1) as n1'. induction 1; inv Heqn1'; eauto using T_S.
Qed.

Lemma appCross_correct A B s t : (s el A /\ t el B) <-> (app s t) el appCross A B.
Proof.
  split.
  - induction A; simpl; intuition; subst; eauto using in_map. 
  - induction A; simpl; try rewrite in_app_iff in *; intros H; try tauto; destruct H as [H1 | H2]; intuition; rewrite in_map_iff in *; destruct H1; destruct H; [left|]; congruence. 
Qed.

Lemma T_var n : #n el T n.
Proof. 
  destruct n; simpl; auto.
Qed.

Lemma T_app s t n : s el T n -> t el T n -> s t el T (S n).
Proof.
  intros; simpl. decide (s t el T n); auto; simpl.
  rewrite in_app_iff; simpl.
  rewrite in_filter_iff, in_app_iff, <- appCross_correct.
  intuition.
Qed.

Lemma T_el_ge s n m : n >= m -> s el T m -> s el T n.
Proof.
  intros A B; destruct (el_elAt B); eapply elAt_el, T_ge; eassumption.
Qed.

Lemma T_lam s n : s el T n -> lam s el T (S n).
Proof.
  intros; simpl; decide (lam s el T n); auto.
  rewrite in_app_iff; simpl; rewrite in_filter_iff, in_app_iff, in_map_iff.
  right. right. split; try left; eauto.
Qed.

Fixpoint exh_size s := match s with
| #n => n
| app s1 s2 => 1 + exh_size s1 + exh_size s2
| lam s => 1 + exh_size s
end.

Lemma T_exhaustive s : s el (T (exh_size s)).
Proof with
  simpl; repeat rewrite in_app_iff; repeat rewrite in_filter_iff; try rewrite <- appCross_correct; eauto using in_filter_iff, in_app_iff, appCross_correct, el_elAt, elAt_el, T_ge, in_map.
  induction s.
  - destruct n; simpl; auto.
  - eapply T_app; eapply T_el_ge; try eassumption; fold exh_size plus; omega.
  - now eapply T_lam.
Qed.

Lemma T_longenough m : |T m| > m.
  induction m.
  - simpl; omega.
  - simpl. rewrite app_length. simpl. omega.
Qed.

Definition g s := match pos s (T (exh_size s)) with None => 0 | Some n => n end.
Definition g_inv n := match elAt (T n) n with None => #0 | Some n => n end.

Lemma g_inv_g s : g_inv (g s) = s.
Proof.
  unfold g. destruct( pos s (T (exh_size s)) ) eqn:A.
  unfold g_inv. destruct (T n .[ n ] ) eqn:B.
  - eapply pos_elAt in A.
    destruct (lt_eq_lt_dec n (exh_size s)) as [[D | D] | D].
    + eapply T_ge in B. rewrite B in A. now inv A. omega.
    + subst. assert (Some s = Some t) by now rewrite <- A, <- B. congruence.
    + eapply T_ge in A. rewrite A in B. now inv B. omega.
  - eapply nth_error_none in B.
    assert (|T n| > n) by eapply T_longenough. omega.
  - assert (HIn : s el T (exh_size s)) by eapply T_exhaustive.
    eapply el_elAt in HIn; eauto. destruct HIn. eapply elAt_el in H. eapply el_pos in H. destruct H. rewrite H in *; congruence. 
Qed.

Hint Unfold left_inverse injective right_inverse surjective.

Lemma disjoint_symm X (A B : list X) : disjoint A B <-> disjoint B A.
Proof.
  rewrite !disjoint_forall; firstorder.
Qed.

Lemma map_lam A : forall x, x el map lam A -> exists t, x = lam t.
Proof.
  intros x B; rewrite in_map_iff in B; destruct B as [? [B _]]; subst; eauto.
Qed.

Lemma appCross_app A B : forall x, x el appCross A B -> exists s t, x = app s t.
Proof.
  induction A.
  - inversion 1.
  - simpl; intros. rewrite in_app_iff in H. destruct H; eauto. rewrite in_map_iff in H. destruct H as [t [H1 H2]]; eauto; subst; eauto.
Qed.

Lemma T_var_not n m : m > n -> ~ #m el T n.
Proof.
  induction n.
  - destruct m; destruct 2; try omega. congruence. auto.
  - simpl; intros A; rewrite !in_app_iff.
    intros [H | H]. 
    + eapply IHn; now try omega.
    + destruct H as [H | H]. inv H; omega.
      rewrite filter_app in H. rewrite in_app_iff in H.
      destruct H as [H | H]; rewrite in_filter_iff in H; destruct H as [H1 H2].
      * rewrite in_map_iff in H1. destruct H1 as [x [H1 _]]. inv H1.
      * destruct (appCross_app H1) as [s [t H3]]; inv H3.
Qed.

Lemma appCross_dupfree A B : dupfree A -> dupfree B -> dupfree (appCross A B).
Proof with eauto using dupfree; intuition.
  induction 1; intros dpf_B; simpl...
  eapply dupfree_app...
  -eapply disjoint_forall. intros y D Hy. 
  edestruct (appCross_app Hy) as [y1 [y2 Hyy]]; subst. eapply appCross_correct in Hy as []. 
  eapply in_map_iff in D. destruct D as [d [D1 D2]]. inv D1...
  -eapply dupfree_map... congruence. 
Qed.

Lemma dupfree_T : forall n, dupfree (T n).
Proof.
  induction n.
  - simpl. repeat econstructor. eauto.
  - simpl. eapply dupfree_app.
    + eapply disjoint_symm, disjoint_cons. split.
      * eapply T_var_not; omega.
      * rewrite filter_app, disjoint_symm, disjoint_forall.
        intros s A B. eapply in_app_iff in B. destruct B; eapply in_filter_iff in H;rewrite Dec_reflect in *;tauto.
    + eassumption.
    + eapply dupfreeC. rewrite in_filter_iff. 
      intros [A _]. rewrite in_app_iff in A. destruct A.
      eapply map_lam in H. destruct H; inv H.
      eapply appCross_app in H. destruct H as [s [t H]]. inv H.
      eapply dupfree_filter. eapply dupfree_app.
      rewrite disjoint_forall.
      intros x A B. destruct (map_lam A), (appCross_app B) as [x1 [x2 B1]]. subst. inv B1.
      eapply dupfree_map; congruence. 
      now eapply appCross_dupfree.
Qed.

Lemma T_dup n1 n2 m1 m2 x : T n1 .[m1 ] = Some x -> T n2 .[m2] = Some x -> m1 = m2.
Proof.
  destruct (lt_eq_lt_dec n1 n2) as [[H | H] | H]; try subst;
  try eapply lt_le_weak in H;
  eauto using (T_ge), dupfree_elAt, dupfree_T.
Qed.

Lemma g_g_inv n : g(g_inv n) = n.
Proof.
  unfold g_inv. destruct (T n .[ n ] ) eqn:B.
  unfold g. destruct( pos t (T (exh_size t)) ) eqn:A.
  - eapply pos_elAt, T_dup in A; eauto. 
  - assert (HIn : t el T (exh_size t)) by eapply T_exhaustive.
    
    eapply el_elAt in HIn. destruct HIn.
    eapply elAt_el in H. eapply el_pos in H. destruct H. rewrite H in A. congruence.
  - eapply nth_error_none in B.
    assert (|T n| > n) by eapply T_longenough.
    omega.
Qed.

Hint Unfold left_inverse injective surjective g g_inv.

Lemma g_T : bijective g.
Proof. 
  split.
  - eauto using left_inv_inj, g_inv_g. 
  - eauto using right_inv_surjective, g_g_inv.
Qed.


Fixpoint C (n : nat) :=
  match n with
    | 0  => [(0,0)]
    | S n => C n ++ (S n, 0) :: filter (fun x => Dec (not (x el C n))) (map (fun p : nat * nat => let (p1,p2) := p in (p1,S p2)) (C n))
  end.

Lemma sublist_C : forall n : nat, exists x B, C (S n) = C n ++ x :: B.
Proof.
  repeat eexists.
Qed.

Lemma C_S p n m : C n .[ m ] = Some p -> C (S n).[ m ] = Some p.
Proof.
  destruct (sublist_C n) as [x [B H]]. rewrite H. eapply elAt_app.
Qed.

Lemma C_ge p n1 n2 m : n2 >= n1 -> C n1 .[ m ] = Some p -> C n2 .[ m ] = Some p.
Proof.
  remember (S n1) as n1'. induction 1; inv Heqn1'; eauto using C_S.
Qed.

Fixpoint eSize (p : nat * nat) := let (n,m) := p in 1 + n + m.

Lemma C_exhaustive p : p el C( eSize p ).
Proof.
  destruct p as [n m]. induction m.
  - simpl. rewrite plus_0_r. destruct n; simpl; auto.
  - simpl.
    decide ( (n,S m) el C (n + S m) ).
    + auto.
    + eapply in_app_iff. right. right.
      eapply in_filter_iff. split.
      * eapply in_map_iff. exists (n, m). split. reflexivity. assert (n + S m = 1 + n + m) by omega. rewrite H. eassumption.
      * rewrite Dec_reflect. eassumption.
Qed.

Lemma C_longenough n : |C n| > n.
Proof.
  induction n; simpl.
  - omega.
  - rewrite app_length. simpl. omega.
Qed.

Definition c n : nat * nat := match elAt (C n) n with None => (0,0) | Some p => p end.
Definition c_inv p : nat := match pos p (C (eSize p)) with None => 0 | Some p => p end.

Lemma c_c_inv p : c (c_inv p) = p.
Proof.
  unfold c_inv. destruct( pos p (C (eSize p)) ) eqn:A.
  unfold c. destruct (elAt (C n) n ) eqn:B.
  - eapply pos_elAt in A.
    destruct (lt_eq_lt_dec n (eSize p)) as [[D | D] | D].
    + eapply C_ge in B. rewrite B in A. now inv A. omega.
    + subst. cut (Some p = Some p0); try congruence. now rewrite <- A, <- B.
    + eapply C_ge in A. rewrite A in B. now inv B. omega.
  - eapply nth_error_none in B.
    assert (|C n| > n) by eapply C_longenough. omega.
  - assert (HIn : p el C (eSize p)) by eapply C_exhaustive.
    eapply el_elAt in HIn. destruct HIn. eapply elAt_el in H. eapply el_pos in H. destruct H. rewrite H in *. congruence. 
Qed.

Lemma c_surj : surjective c.
  eapply right_inv_surjective. unfold right_inverse. eapply c_c_inv.
Qed.
(*
Definition ESize : term := .\"p"; "p" (.\"n","m"; !Add !!(enc 1) (!Add "n" "m")).

Lemma ESize_correct p : ESize (penc p) == enc(eSize p).
Proof.
  destruct p as [n m]. simpl.
  transitivity (Add (enc 1) (Add (enc n) (enc m))). Lsimpl.
  now rewrite !Add_correct.
Qed.

Definition PEq : term := .\"p1", "p2"; "p1" (.\"n1", "m1"; "p2" (.\"n2", "m2"; !Andalso (!EqN "n1" "n2") (!EqN "m1" "m2"))).

Lemma PEq_rec n1 m1 n2 m2 : PEq (penc (n1,m1)) (penc (n2,m2)) == Andalso (EqN (enc n1) (enc n2)) (EqN (enc m1) (enc m2)).
Proof.
  Lsimpl.
Qed.

Lemma PEq_correct p1 p2 : PEq (penc p1) (penc p2) == true /\ p1 = p2 \/ PEq (penc p1) (penc p2)  == false /\ p1 <> p2.
Proof.
  destruct p1 as [n1 m1], p2 as [n2 m2].
                                   
  destruct (EqN_correct n1 n2) as [[E1 H1] | [E1 H1]],
           (EqN_correct m1 m2) as [[E2 H2] | [E2 H2]]; rewrite PEq_rec;
  [ left; split; [Lsimpl | congruence] | right; split; [Lsimpl | congruence] .. ].
Qed.

Definition CC := lam (R (.\ "C", "n"; "n" !(lenc penc [(0,0)]) (.\"n"; !Append ("C" "n")
                                                           (!Cons (!Pair (!Succ "n") !(enc 0))
                                                             (!Filter (.\ "x"; !Not (!(El PEq) "x" ("C" "n")))
                                                               (!Map (.\"p"; "p" (.\"n","m"; !Pair "n" (!Succ "m"))) ("C" "n")))))) 0).

Lemma CC_closed : closed CC.
Proof.
  Lproc.
Qed.

Lemma CC_lam : lambda CC.
Proof.
  Lproc.
Qed.

Hint Resolve CC_closed CC_lam :cbv.


Lemma CC_rec_0 : CC (enc 0) == lenc penc [(0,0)].
Proof.
  Lsimpl.
Qed.

Lemma CC_rec_S n : CC (enc (S n)) == Append (CC (enc n)) (Cons (Pair (Succ (enc n)) (enc 0))
                                                               (Filter (lam (Not (El PEq 0 (CC (enc n)))))
                                                                       (Map (lam (0 (lam(lam(Pair 1 (Succ 0)))))) (CC (enc n))))).
Proof.
  Lsimpl.
Qed.
                                                         
Lemma CC_correct n : CC (enc n) == lenc penc (C n).
Proof with ( intros; Lproc; eauto with cbv ).
  induction n.
  - now rewrite CC_rec_0.
  - rewrite CC_rec_S. setoid_rewrite IHn at 1 3.
    rewrite Map_correct with (f := (fun p : nat * nat => let (p1,p2) := p in (p1,S p2)))...
    rewrite Filter_correct with (p := (fun x => not (x el C n)))...
    rewrite Succ_correct, Pair_correct, Cons_correct, Append_correct; try (simpl; reflexivity)...
    + destruct El_correct with (s := x) (A := C n) (enc := penc) (Eq := PEq) as [[H1 H2] | [H1 H2]]...
      * eapply PEq_correct.
      * right. split;[|firstorder].
        transitivity (Not (((El PEq) (penc x)) (CC (enc n)))). clear IHn H1. Lsimpl. rewrite IHn,H1. apply not_rec_true.
      * left;split;[|firstorder].
        transitivity (Not (((El PEq) (penc x)) (CC (enc n)))). clear IHn H1;Lsimpl. rewrite IHn,H1. apply not_rec_false.
    + split; Lproc.
      intros p. destruct p as [n1 m1]. clear IHn. Lsimpl.
Qed.

Definition Cn : term := (.\"n";
  (!Nth (!CC "n") "n") !I !(penc (0,0))).

Lemma Cn_closed : closed Cn.
Proof.
  Lproc.
Qed.

Hint Unfold Cn : cbv.
Hint Rewrite Cn_closed : cbv.

Lemma Cn_correct n : Cn (enc n) == penc(c n).
Proof.
  transitivity (Nth (CC (enc n)) (enc n) I (penc (0,0))). Lsimpl.
  rewrite CC_correct. unfold penc.
  rewrite Nth_correct; Lproc.
  unfold c, elAt, oenc.
  destruct (nth_error (C n) n); Lsimpl.
  intros; Lproc. intros; Lproc.
Qed.  
 *) 
