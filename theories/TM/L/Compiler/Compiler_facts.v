From Undecidability Require Import L.Datatypes.LBool L.Datatypes.Lists L.Tactics.LTactics L.Util.L_facts.

Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypes Undecidability.Shared.Libs.PSL.Vectors.Vectors.
Require Import Vector List.

Require Import Undecidability.TM.Util.TM_facts.

From Undecidability Require Import ProgrammingTools.
From Undecidability Require Import TM.TM.

From Undecidability Require Import L.L TM.TM.
Require Import List.
Import ListNotations.

Import VectorNotations.

From Undecidability.TM.L.Compiler Require Import Compiler_spec AddToBase.

Require Import Equations.Prop.DepElim.
      
Definition L_computable_bool_closed {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) := 
  exists s, closed s /\ forall v : Vector.t (list bool) k, 
      (forall m, R v m <-> L.eval (Vector.fold_left (fun s n => L.app s (encL n)) s v) (encL m)) /\
      (forall o, L.eval (Vector.fold_left (fun s n => L.app s (encL n)) s v) o -> exists m, o = encL m).

Lemma L_computable_bool_can_closed k R:
  L_computable_bool_closed R <-> L_computable (k:=k) R.
Admitted.

Lemma nth_error_to_list {X n} (v : Vector.t X n) i k :
  k = (proj1_sig (Fin.to_nat i)) ->
  nth_error (Vector.to_list v) k = Some (Vector.nth v i).
Proof.
  intros ->. induction v; cbn.
  - inversion i.
  - dependent destruct i; cbn.
    + reflexivity.
    + destruct (Fin.to_nat p) as (i, P) eqn:E. cbn.
      fold (to_list v).
      specialize (IHv (Fin.of_nat_lt P)). cbn in *.
      rewrite Fin.to_nat_of_nat in IHv. cbn in IHv.
      now rewrite <- (Fin.of_nat_to_nat_inv p), E. 
Qed.

Lemma encTM_inj {Σ} (sym_s sym_b : Σ) n1 n2 :
  sym_s <> sym_b -> encTM sym_s sym_b n1 = encTM sym_s sym_b n2 -> n1 = n2.
Proof.
  intros Hdiff.
  induction n1 in n2 |- *.
  - destruct n2; now inversion 1.
  - destruct n2; inversion 1.
    destruct a, b.
    + f_equal. eapply IHn1. unfold encTM. congruence.
    + now exfalso.
    + now exfalso.
    + f_equal. eapply IHn1. unfold encTM. congruence.
Qed.

From Undecidability.TM Require Import Hoare.

Definition TM_computable_hoare_in {k n Σ} s b (v: Vector.t (list bool) k): SpecV Σ (k+1+n)
  := (Vector.map (fun bs => Custom (eq (encTM s b bs))) v ++ [Custom (eq niltape)]) ++ Vector.const (Custom (eq niltape)) _.

Lemma TM_computable_hoare_in_spec {k n Σ} (s b:_ + Σ) (v: Vector.t (list bool) k): 
  (Vector.map (encTM s b) v ++ [niltape]) ++ const niltape n
    ≃≃ ([]%list, TM_computable_hoare_in s b v).
Proof.
  eapply tspecI;cbn;[easy|]; unfold TM_computable_hoare_in;intros i;
  destruct_fin i;cbn;repeat (rewrite Vector_nth_L + rewrite Vector_nth_R + rewrite nth_map' + rewrite const_nth);cbn; reflexivity.
Qed.


Definition TM_computable_hoare_out {k n Σ} s b (bs :list bool): SpecV Σ (k+1+n)
  := (Vector.const (Custom (fun _ => True)) _ ++ [Custom (eq (encTM s b bs)) ])++ Vector.const (Custom (fun _ => True)) _.

Lemma TM_computable_hoare_out_spec {k n Σ} (s b:_ + Σ) bs t': 
  t' ≃≃ ([]%list, TM_computable_hoare_out (k:=k) (n:=n)s b bs)
  -> nth_error (to_list t') k = Some (encTM s b bs).
Proof.
  intros ([]&Hm2)%tspecE. specialize (Hm2 (Fin.L n (Fin.R k Fin0))).
  unfold TM_computable_hoare_out in Hm2. rewrite Vector_nth_L,Vector_nth_R in Hm2.
  cbn in Hm2. setoid_rewrite Hm2. erewrite nth_error_to_list. reflexivity.
  rewrite Fin.L_sanity,Fin.R_sanity. easy. 
Qed.


Definition TM_computable_hoare {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) := 
  exists n : nat, exists Σ : finType, exists s b , s <> b /\ 
    exists M : pTM (Σ^+) unit (k + 1 + n),
    forall v, 
      Triple ≃≃([],TM_computable_hoare_in s b v) M (fun y t => exists res, t ≃≃ ([R v res]%list,TM_computable_hoare_out s b res))
      /\ forall res, R v res ->
          exists k__steps, TripleT ≃≃([],TM_computable_hoare_in s b v) k__steps M (fun y => ≃≃([]%list,TM_computable_hoare_out s b res)).
  
Lemma TM_computable_hoare_spec k R :
  functional R ->
  @TM_computable_hoare k R -> @TM_computable k R.
Proof.
  intros Hfun (n & Σ & s & b & Hdiff & [M lab] & H).
  eexists n, _, s, b. split. exact Hdiff. exists M.
  intros v. specialize (H v) as [H1 H2]. split.
  - intros m. split.
    + intros HR.
      specialize H2 as [k__steps H2%TripleT_TerminatesIn]. eassumption.
      cbn in H2.
      destruct (H2 ((Vector.map (encTM s b) v ++ [niltape]) ++ Vector.const niltape n) k__steps) as [[q' t'] Hconf].
      * split. 2:easy. now apply TM_computable_hoare_in_spec.        
      * exists q', t'. split. eapply TM_eval_iff. eexists. eapply Hconf.
        eapply H1 in Hconf as (m' & Hm1 & Hm2%TM_computable_hoare_out_spec).
        now apply TM_computable_hoare_in_spec.
        pose proof (Hfun _ _ _ HR Hm1) as ->.
        easy.
    + intros (q' & t' & [steps Hter] % TM_eval_iff & Hout).
      eapply H1 in Hter as (m' & Hm1 & Hm2%TM_computable_hoare_out_spec).
      now apply TM_computable_hoare_in_spec.
      cbn -[to_list] in *.
      enough (m = m') by now subst.
      eapply encTM_inj; eauto. congruence.
  - intros q t [steps Hter] % TM_eval_iff.
    eapply H1 in Hter as (m & Hm1 & Hm2%TM_computable_hoare_out_spec).
    now apply TM_computable_hoare_in_spec. eauto.
Qed.



(** * The tape-order is different than in the implemented machine, so here again with the tape-order implemented: *)
Definition TM_computable_hoare_in' {k n Σ} s b (v: Vector.t (list bool) k): SpecV Σ (1+n+k)
  := Custom (eq niltape) :: Vector.const (Custom (eq niltape)) _ ++ Vector.map (fun bs => Custom (eq (encTM s b bs))) v.

Definition TM_computable_hoare_out' {n Σ} s b (bs :list bool): SpecV Σ (1+n)
  := Custom (eq (encTM s b bs)) :: Vector.const (Custom (fun _ => True)) _.

Definition TM_computable_hoare' {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) := 
  exists n : nat, exists Σ : finType, exists s b , s <> b /\ 
    exists M : pTM (Σ^+) unit (1 + n + k),
    forall v, 
      Triple ≃≃([],TM_computable_hoare_in' s b v) M (fun y t => exists res, t ≃≃ ([R v res]%list,TM_computable_hoare_out' s b res))
      /\ forall res, R v res ->
          exists k__steps, TripleT ≃≃([],TM_computable_hoare_in' s b v) k__steps M (fun y => ≃≃([]%list,TM_computable_hoare_out' s b res)).



Local Definition tapeOrderSwap n k:=
(Fin.L n (Fin.R k Fin0) :::  tabulate (n := n) (fun x => Fin.R (k + 1) x) ++ (tabulate (n := k) (fun x => Fin.L n (Fin.L 1 x)))).

Local Lemma tapeOrderSwap_dupfree k n : VectorDupfree.dupfree (tapeOrderSwap n k).
Proof.
  unfold tapeOrderSwap.
  econstructor. intros [ [i Hi % (f_equal (fun x => proj1_sig (Fin.to_nat x)))] % in_tabulate | [i Hi % (f_equal (fun x => proj1_sig (Fin.to_nat x)))] % in_tabulate ] % Vector_in_app.
  3: eapply Vector_dupfree_app; repeat split.
  + rewrite Fin.L_sanity, !Fin.R_sanity in Hi. cbn in Hi. lia.
  + rewrite !Fin.L_sanity, !Fin.R_sanity in Hi. destruct (Fin.to_nat i); cbn in *; lia.
  + eapply dupfree_tabulate_injective. eapply Fin_R_fillive.
  + eapply dupfree_tabulate_injective. intros. eapply Fin_L_fillive. eapply Fin_L_fillive. eassumption.
  + intros ? (? & ?) % in_tabulate (? & ?) % in_tabulate. subst.
    eapply (f_equal (fun H => proj1_sig (Fin.to_nat H))) in H0. rewrite Fin.R_sanity, !Fin.L_sanity in H0.
    destruct Fin.to_nat, Fin.to_nat. cbn in *. lia.
Qed.

Lemma TM_computable_hoare_in'_spec {k n Σ} s b (v: Vector.t (list bool) k):
  TM_computable_hoare_in' (Σ:=Σ) s b v = Downlift (TM_computable_hoare_in s b v) (tapeOrderSwap n k).
Proof.
  unfold TM_computable_hoare_in,TM_computable_hoare_in'.
  eapply eq_nth_iff';intros i.
  destruct_fin i;cbn.
  all:repeat (rewrite Vector_nth_L + rewrite Vector_nth_R + rewrite nth_map' + rewrite nth_tabulate + rewrite const_nth + cbn);cbn.
  all:reflexivity.
Qed.


Lemma helper n m' m f: 
injective f ->
  lookup_index_vector (n:=n)
(tabulate (fun i : Fin.t m' => f i)) 
(f m) = Some m.
Proof.
revert n m f. induction m';cbn. easy.
intros n m f Hinj. specialize (Fin.eqb_eq _ (f m) (f Fin0)) as H'.
destruct Fin.eqb.
-destruct H' as [H' _]. specialize (H' eq_refl). apply Hinj in H' as ->. easy.
-destruct H' as [_ H']. destruct (fin_destruct_S m) as [[i' ->]| ->]. 2:now discriminate H'.
 specialize IHm' with (f:= fun m => f (Fin.FS m) ). cbn in IHm'. rewrite IHm'. easy. intros ? ? ?%Hinj. now apply Fin.FS_inj.
Qed.


Lemma Fin_eqb_R_R  m n (i i' : Fin.t n):
  Fin.eqb (Fin.R m i) (Fin.R m i') = Fin.eqb i i'.
Proof. induction m;cbn. all:congruence. Qed.

Lemma Fin_eqb_L_L m n (i i' : Fin.t n):
  Fin.eqb (Fin.L m i) (Fin.L m i') = Fin.eqb i i'.
Proof.
  revert i i'. induction n;intros i i'; destruct_fin i;destruct_fin i';cbn.
  4:rewrite !Nat.eqb_refl. all:congruence.
Qed.


Lemma Fin_eqb_R_L m n (i : Fin.t n) (i' : Fin.t m):
  Fin.eqb(Fin.R n i')  (Fin.L m i)  = false.
Proof.
  revert m i i'. induction n;intros m i i'; destruct_fin i;destruct_fin i';cbn.
  all:easy.
Qed. 

Lemma Fin_eqb_L_R m n (i : Fin.t n) (i' : Fin.t m):
  Fin.eqb (Fin.L m i) (Fin.R n i') = false.
Proof.
  revert m i i'. induction n;intros m i i'; destruct_fin i;destruct_fin i';cbn.
  all:easy.
Qed. 

Lemma TM_computable_hoare_out'_spec {k n Σ} s b bs w:
  TM_computable_hoare_out (Σ:=Σ) s b bs = Frame w (tapeOrderSwap n k) (TM_computable_hoare_out' s b bs).
Proof.
  unfold TM_computable_hoare_out,TM_computable_hoare_out'.
  eapply eq_nth_iff';intros i. unfold Frame,fill.
  rewrite nth_tabulate.
  destruct_fin i;cbn.
  all:repeat (rewrite Vector_nth_L + rewrite Vector_nth_R + rewrite nth_map' + rewrite nth_tabulate + rewrite const_nth + cbn);cbn.
  all:repeat (rewrite Fin_eqb_L_L + rewrite Fin_eqb_L_R  + rewrite Fin_eqb_R_L + rewrite Fin_eqb_R_R +cbn);cbn.
  2:easy.
  all:erewrite lookup_index_vector_Some;cbn;[now rewrite const_nth| |].
  2:now rewrite Vector_nth_R,nth_tabulate.
  3:now rewrite Vector_nth_L,nth_tabulate.
  all:eapply dupfree_cons. all:apply tapeOrderSwap_dupfree. 
Qed.

Lemma TM_computable_hoare'_spec k R :
  functional R ->
  @TM_computable_hoare' k R -> TM_computable R.
Proof.
  intros Hfun (n & Σ & s & b & Hdiff & M & H).
  eapply TM_computable_hoare_spec. eassumption.
  exists n, Σ, s, b. split. exact Hdiff.
  eexists (LiftTapes M (tapeOrderSwap n k)).
  intros v. specialize (H v) as [H1 H2].
  rewrite TM_computable_hoare_in'_spec in H1,H2.
  split.
  - refine (Consequence _ _ _). refine (LiftTapes_Spec_ex _ _). now apply tapeOrderSwap_dupfree.
    exact H1. reflexivity. cbn. intro. eapply EntailsI. intros ? []. eexists.
    erewrite TM_computable_hoare_out'_spec. eassumption.
  - intros. specialize H2 as [x H2]. easy. exists x.
    refine (ConsequenceT _ _ _ _). refine (LiftTapes_SpecT _ _). now apply tapeOrderSwap_dupfree.
    exact H2. reflexivity. cbn. now rewrite <- TM_computable_hoare_out'_spec. easy.
Qed. 

Lemma closed_compiler_helper s n v: closed s ->
closed
  (Vector.fold_left (n:=n)
     (fun (s0 : term) (l_i : list bool) => L.app s0 (encL l_i)) s v).
Proof.
  revert s. depind v. all:cbn. easy.
  intros. eapply IHv. change (encL h) with (enc h). Lproc.
Qed. 
