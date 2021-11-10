From Equations Require Import Equations.
From Undecidability.Shared.Libs.PSL Require Import Vectors.

From Coq Require Import Vector List.

From Undecidability.L Require Import L LTactics L_facts Functions.Eval Functions.Decoding Functions.Encoding.
From Undecidability.L.Datatypes Require Import LBool Lists LVector List.List_fold.
From Undecidability.L.Complexity.LinDecode Require Import LTDbool LTDlist LTDnat.

From Undecidability.TM.L.CompilerBoolFuns Require Import Compiler_spec NaryApp ClosedLAdmissible Compiler_facts.

Import ListNotations.
Import VectorNotations.
Import L_Notations. 

Lemma encBools_nat_TM {Σ} n (s b : Σ) :
encNatTM s b n = encBoolsTM s b (List.repeat true n).
Proof.
unfold encNatTM, encBoolsTM. f_equal.
induction n; cbn.
- reflexivity.
- f_equal. eapply IHn.
Qed.

(* Section Fix_X.
Variable (X:Type).
Context {intX : registered X}.

Global Instance term_repeat: computable (@repeat X).
Proof using intX.
  extract.
Qed.

Global Instance term_length: computable (@length X).
Proof using intX.
  extract.
Qed.

End Fix_X. *)

Fixpoint gen_list {k} {X} {Hr : registered X} (v : Vector.t nat k) : term :=
match v with
| [] => ext (@nil X)
| n :: v => ext (@Datatypes.cons X) (var n) (@gen_list _ X Hr v)
end.

Lemma subst_gen_list {k} {X} {Hr : registered X} u n :
n >= k ->
subst (gen_list (X := X) (many_vars k)) n u = gen_list (X := X) (many_vars k).
Proof.
induction k in n |- *; rewrite ?many_vars_S; cbn.
- rewrite subst_closed. 2:Lproc. reflexivity.
- intros Hn. rewrite subst_closed. 2: Lproc. destruct (Nat.eqb_spec k n); try lia.
  rewrite IHk. reflexivity. lia.
Qed.

Lemma gen_list_spec {k} {X} {Hr : registered X} (v' : Vector.t X k) :
many_subst (gen_list (X := X) (many_vars k)) 0 (Vector.map enc v') == enc v'.
Proof.
induction v'; cbn - [many_vars].
- Lsimpl_old.
- rewrite many_vars_S. cbn. rewrite Nat.eqb_refl.
  rewrite subst_closed; [ | now Lproc ]. rewrite subst_gen_list; try lia.
  rewrite many_subst_app. rewrite many_subst_closed. 2:Lproc. rewrite IHv'.
  unfold enc at 2. cbn. now Lsimpl.
Qed.

Definition validate (l : list (list bool)) := forallb (forallb (fun x => x)) l.

Lemma validate_spec_help (l : list bool) : forallb (fun x => x) l <-> exists l', l = List.repeat true l'.
Proof.
induction l; cbn.
- firstorder. now exists 0.
- split.
  + intros [-> [n ->] % IHl] % andb_true_iff. now exists (S n).
  + intros [[ | n] [= -> ->]]. cbn. eapply IHl. eauto.
Qed.

Lemma validate_spec {k} (v : Vector.t (list bool) k) :
validate (Vector.to_list v) = true <-> exists v', v = Vector.map (List.repeat true) v'.
Proof.
induction v; cbn; try fold (Vector.to_list v) in *; try fold (validate (Vector.to_list v)) in *.
- split; try congruence. intros _. now exists [].
- split.
  + intros [H1 [v' ->] % IHv] % andb_true_iff. eapply validate_spec_help in H1 as [m ->].
    now exists (m :: v').
  + intros (v' & H). dependent elimination v'. cbn in H.
    eapply Vector.cons_inj in H as [-> ->]. eapply andb_true_iff. split.
    * clear. rename h0 into n. induction n; cbn; congruence.
    * eapply IHv. eauto.
Qed.

Lemma validate_spec' {k} (v : Vector.t nat k) :
validate (Vector.to_list (Vector.map (List.repeat true) v)) = true.
Proof.
eapply validate_spec. eauto.
Qed.

Definition idbool := (fun x : bool => x).
Definition forallb' := @forallb bool.
Definition alltrue x :=  idbool x.
Definition forallb'' := @forallb (list bool).

Local Instance term_forallb' : computable forallb' | 0.
Proof.
  unfold forallb'.
  extract.
Qed.

Local Instance term_forallb'' : computable forallb'' | 0.
Proof.
  unfold forallb''.
  extract.
Qed.

#[global]
Instance term_idbool : computable idbool.
Proof.
  extract.
Qed.

#[global]
Instance term_alltrue : computable alltrue.
Proof.
  extract.
Qed.

#[export] Remove Hints term_forallb : typeclass_instances.

#[global]
Instance term_validate : computable validate.
Proof.
  change (computable (fun l => forallb'' (forallb' alltrue) l)).
  extract.
Qed.

Lemma forall_proc_help {X} {H : registered X} {k} {v : Vector.t X k} : forall x, Vector.In x (Vector.map enc v) -> proc x.
Proof.
  clear. induction v; cbn; intros ? Hi. inversion Hi. inv Hi. Lproc. eapply IHv. eapply Eqdep_dec.inj_pair2_eq_dec in H3. subst. eauto. eapply nat_eq_dec.
Qed.

Lemma L_computable_to_L_bool_computable k (R : Vector.t nat k -> nat -> Prop) : 
L_computable R -> L_bool_computable (fun v m => exists v' m', v = Vector.map (List.repeat true) v' /\ m = List.repeat true m' /\ R v' m').
Proof.
    intros (s & Hcl & Hs) % L_computable_can_closed. setoid_rewrite <- many_app_eq_nat in Hs.
    pose (sim := many_lam k (ext validate (gen_list (X := list bool) (many_vars k)) (lam (ext (@repeat bool) (ext true) 0)) (lam Omega) (many_app s (Vector.map (fun r => ext (@length bool) (var r)) (many_vars k)))) ).
    exists sim.
    intros v. setoid_rewrite <- many_app_eq. 
    assert (HEQ : many_app sim (Vector.map enc v) ==  enc (validate (Vector.to_list v)) (lam (ext (repeat (A := bool)) (ext true) 0)) (lam Omega) (many_app s (Vector.map enc (Vector.map (@List.length bool) v)))).
    { unfold sim. rewrite many_beta. 2: eapply forall_proc_help.
      rewrite !many_subst_app. rewrite gen_list_spec. rewrite !many_subst_many_app. repeat (rewrite many_subst_closed; [ | now Lproc]).
      rewrite Vector.map_map. unfold enc at 1. cbn. Lsimpl. eapply equiv_R.
      match goal with |- context [ VectorDef.map ?f ?v] => unshelve eassert (many_app s (VectorDef.map f v) == _) as -> end.
      refine (many_app s (Vector.map (@enc nat _) (Vector.map (@List.length bool) v))).
      * clear. induction v in s |- *.
        -- reflexivity.
        -- rewrite many_vars_S. cbn -[many_subst]. rewrite equiv_many_app_L. 2:{ cbn. rewrite Nat.eqb_refl. rewrite subst_closed. 2:Lproc. rewrite many_subst_closed. 2: Lproc.
           Lsimpl. reflexivity. }
           rewrite <- IHv. match goal with [ |- ?l == ?r ] => enough (l = r) as H by now rewrite H end. cbn.
           f_equal. eapply Vector.map_ext_in. intros a Ha. rewrite subst_closed. 2:Lproc. rewrite !many_subst_app. rewrite many_subst_closed. 2:Lproc.
           destruct (Nat.eqb_spec a n).
           ++ subst. eapply many_var_in in Ha. lia.
           ++ reflexivity. 
      * reflexivity.
    }
    split.
    - intros m. split.
      + intros (v' & m' & -> & -> & HR).
        eapply Hs in HR. eapply eval_iff in HR. rewrite eval_iff.
        rewrite HEQ. Lsimpl. change (encNatL m') with (enc m') in HR. change (encBoolsL) with (@enc (list bool) _).
        rewrite validate_spec'.
        rewrite !Vector.map_map. erewrite Vector.map_ext. 2:intros; now rewrite repeat_length. Lsimpl_old.
      + rewrite eval_iff. rewrite HEQ. erewrite equiv_eval_equiv. 2:{ Lsimpl. reflexivity. }
        intros Heval. change (encNatL) with (@enc nat _) in *. change (encBoolsL) with (@enc (list bool) _) in *.
        match type of Heval with L_facts.eval ?l _ => assert (Hc : converges l) by eauto end.
        eapply app_converges in Hc as [H1 Hc]. eapply eval_converges in Hc as [o Hc % eval_iff].   
        pose proof (Hc' := Hc). eapply eval_iff in Hc'.
        eapply Hs in Hc as [m' ->].
        destruct (validate (to_list v)) eqn:E.
        * clear HEQ. rewrite Hc' in Heval.
          erewrite equiv_eval_equiv in Heval. 2:{ clear Heval.  Lsimpl. reflexivity. }  eapply validate_spec in E as [v' ->].
          eexists v'.
          assert (m = repeat true m') as ->. { eapply encBoolsL_inj. change (encBoolsL) with (@enc (list bool) _).
          eapply unique_normal_forms;[Lproc..|]. now destruct Heval as [-> _]. } 
          exists m'. repeat split.  eapply Hs.
          rewrite !Vector.map_map in *. erewrite Vector.map_ext in *. 2:intros; now rewrite repeat_length. 2: reflexivity.
          now eapply eval_iff.
        * erewrite equiv_eval_equiv in Heval. 2:{ clear Heval. rewrite Hc'. eapply beta_red. Lproc. rewrite subst_closed. 2:Lproc. reflexivity. } 
          now eapply Omega_diverge in Heval.
    - intros o. rewrite eval_iff. rewrite HEQ. erewrite equiv_eval_equiv. 2:{ Lsimpl. reflexivity. }
      intros Heval. change (encNatL) with (@enc nat _) in *. change (encBoolsL) with (@enc (list bool) _) in *.
      match type of Heval with L_facts.eval ?l _ => assert (Hc : converges l) by eauto end.
      eapply app_converges in Hc as [H1 Hc]. eapply eval_converges in Hc as [o' Hc % eval_iff].   
      pose proof (Hc' := Hc). eapply eval_iff in Hc'.
      eapply Hs in Hc as [m' ->].
      destruct (validate (to_list v)) eqn:E.
      * clear HEQ. erewrite equiv_eval_equiv in Heval. 2:{ clear Heval. Lsimpl. reflexivity. } eapply validate_spec in E as [v' ->].
        rewrite !Vector.map_map in *. erewrite Vector.map_ext in *. 2:intros; now rewrite repeat_length.
        exists (repeat true m'). destruct Heval as [Heval ?].
        eapply unique_normal_forms;[Lproc..|]. now rewrite Heval.
      * erewrite equiv_eval_equiv in Heval. 2:{ clear Heval. rewrite Hc'. eapply beta_red. Lproc. rewrite subst_closed. 2:Lproc. reflexivity. } 
        now eapply Omega_diverge in Heval.
      Unshelve. 
Qed.

Lemma TM_bool_computable_to_TM_computable k (R : Vector.t nat k -> nat -> Prop) : 
TM_bool_computable (fun v m => exists v' m', v = Vector.map (List.repeat true) v' /\ m = List.repeat true m' /\ R v' m') -> TM_computable R.
Proof.
    unfold TM_computable. 
    intros (n & Σ & s & b & Hsb & M & H).
    exists n, Σ, s, b. split. exact Hsb. exists M.
    intros v. split.
    - intros m. split.
      + intros HR. specialize (H (Vector.map (repeat true) v)) as [H1 H2]. specialize (H1 (repeat true m)) as [(q & t & H1) _].
        * exists v, m. repeat split. eassumption.
        * exists q, t. rewrite !encBools_nat_TM. erewrite Vector.map_ext. 2: intros; eapply encBools_nat_TM. rewrite Vector.map_map in H1. exact H1.
      + intros (q & t & H1). rewrite !encBools_nat_TM in H1. erewrite Vector.map_ext in H1. 2: intros; eapply encBools_nat_TM.
        specialize (H (Vector.map (repeat true) v)) as [H2 _]. specialize (H2 (repeat true m)) as [_ (v' & m' & Hv' & Hm' & HR)].
        * exists q, t. rewrite Vector.map_map. eapply H1.
        * eapply (f_equal (@length bool)) in Hm'. rewrite !repeat_length in Hm'. subst. 
          clear - Hv' HR. induction v ; dependent elimination v'. exact HR. inversion Hv'.
          eapply (f_equal (@length bool)) in H0. rewrite !repeat_length in H0. subst. eapply IHv.
          2:eassumption. eapply Eqdep_dec.inj_pair2_eq_dec in H1. eassumption. eapply nat_eq_dec.
    - intros q t H1. erewrite Vector.map_ext in H1. 2: intros; eapply encBools_nat_TM.
      destruct (H (Vector.map (repeat true) v)) as [H3 [m H2]].
      * rewrite Vector.map_map. eapply H1.
      * exists (length m). rewrite H2. rewrite encBools_nat_TM. specialize (H3 m) as [_ (v' & m' & ? & -> & H3)].
        -- exists q, t. split; eauto. rewrite Vector.map_map. exact H1.
        -- now rewrite repeat_length.
Qed.
