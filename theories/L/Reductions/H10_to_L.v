From Undecidability.H10 Require Import H10 dio_single dio_logic.
Require Import Undecidability.PCP.Util.PCP_facts.
Require Import Undecidability.Shared.Libs.PSL.FiniteTypes Undecidability.Shared.Libs.PSL.FiniteTypes.Arbitrary.
From Undecidability.Synthetic Require Export DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability.L.Datatypes Require Import LNat Lists LProd.
From Undecidability.L Require Import Tactics.LTactics Computability.MuRec Computability.Synthetic Tactics.GenEncode.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos.
Import ListAutomationNotations.

Require Import Nat Datatypes.

(* * Diophantine Equations *)

Inductive poly : Set :=
    poly_cnst : nat -> poly 
  | poly_var : nat -> poly 
  | poly_add : poly -> poly -> poly
  | poly_mul : poly -> poly -> poly.

MetaCoq Run (tmGenEncode "enc_poly" poly).
#[export] Hint Resolve enc_poly_correct : Lrewrite.

Instance term_poly_cnst: computable poly_cnst. Proof. extract constructor. Qed.
Instance term_poly_var : computable poly_var. Proof. extract constructor. Qed.
Instance term_poly_add : computable poly_add. Proof. extract constructor. Qed.
Instance term_poly_mul : computable poly_mul. Proof. extract constructor. Qed.

Fixpoint eval (p : poly) (L : list nat) :=
  match p with
  | poly_cnst n => n
  | poly_var n => nth n L 0
  | poly_add p1 p2 => eval p1 L + eval p2 L
  | poly_mul p1 p2 => eval p1 L * eval p2 L
  end.
Instance term_eval : computable eval. Proof. extract. Qed.

Definition poly_add' '(x,y) : poly  := poly_add x y.
Instance term_poly_add' : computable poly_add'. Proof. extract. Qed.

Definition poly_mul' '(x,y) : poly := poly_mul x y.
Instance term_poly_mul' : computable poly_mul'. Proof. extract. Qed.

Fixpoint L_poly n : list (poly) :=
  match n with
  | 0 => []
  | S n => L_poly n ++  map poly_cnst (L_nat n)
                                   ++ map poly_var (L_nat n)
                                   ++ map poly_add' (list_prod (L_poly n) (L_poly n))
                                   ++ map poly_mul' (list_prod (L_poly n) (L_poly n))
  end.
  
Instance term_L_poly : computable L_poly. Proof. extract. Qed.

Instance enum_poly :
  list_enumerator__T L_poly poly.
Proof.
  intros p. induction p.
  + destruct (el_T n) as [m].
    exists (1 + m). cbn. in_app 2. in_collect n. exact H.
  + destruct (el_T n) as [m].
    exists (1 + m). cbn. in_app 3. eauto.
  + destruct IHp1 as [m1]. destruct IHp2 as [m2].
    exists (1 + m1 + m2). cbn. in_app 4. in_collect (p1, p2); eapply cum_ge'; eauto; lia.
  + destruct IHp1 as [m1]. destruct IHp2 as [m2].
    exists (1 + m1 + m2). cbn. in_app 5. in_collect (p1, p2); eapply cum_ge'; eauto; lia.
Defined. (* because instance *)

Fixpoint conv n (p : dio_single.dio_polynomial (pos n) (pos 0)) : poly.
Proof.
  destruct p as [ | p | p | ].
  - exact (poly_cnst n0).
  - exact (poly_var (pos.pos2nat p)).
  - invert pos p.
  - destruct d.
    + exact (poly_add (conv _ p1) (conv _ p2)).
    + exact (poly_mul (conv _ p1) (conv _ p2)).
Defined. (* because term *)

Fixpoint L_from (n : nat) : (pos n -> nat) -> list nat.
Proof.
  intros phi. destruct n.
  - exact [].
  - refine (_ :: L_from _ _)%list.
    + exact (phi pos.pos_fst).
    + intros. eapply phi. econstructor 2. exact H.
Defined. (* because term *)


Lemma L_nth n phi (p : pos n) : nth (pos2nat p) (L_from phi) 0 = phi p.
Proof.
  induction n.
  - invert pos p.
  - cbn. invert pos p.
    + cbn. now rewrite pos.pos2nat_fst.
    + now rewrite pos.pos2nat_nxt, IHn.
Qed.
  
Lemma phi_to_L n : forall phi, forall p, dp_eval phi (fun _ => 0) p = eval (@conv n p) (L_from phi).
Proof.
  induction p; cbn.
  - reflexivity.
  - now rewrite L_nth.
  - invert pos p.
  - destruct d; cbn; congruence.
Qed.

Lemma eval_L_from n p L :
  eval (@conv n p) (L_from (fun p : pos n => nth (pos2nat p) L 0)) = eval (conv p) L.
Proof.
  induction p; cbn.
  - reflexivity.
  - revert L; induction n; intros; cbn.
    + invert pos v.
    + invert pos v.
      * rewrite pos2nat_fst. reflexivity.
      * rewrite pos2nat_nxt in *.
        destruct L.
        -- cbn. clear. induction n.
           ++ cbn. invert pos v.
           ++ cbn. invert pos v. rewrite !pos.pos2nat_fst.
              now rewrite pos.pos2nat_nxt.
              now rewrite pos.pos2nat_nxt.
        -- cbn. now rewrite <- IHn with (L := L).
  - invert pos p.
  - destruct d; cbn; congruence.
Qed.      
    
Lemma red :
  H10 ⪯ (fun '(p1, p2) => exists L, eval p1 L = eval p2 L).
Proof.
  unshelve eexists.
  - intros (n & p1 & p2). exact (conv p1, conv p2).
  - intros (n & p1 & p2). cbn.
    unfold dio_single_pred. cbn. split.
    + intros [phi]. exists (L_from phi). now rewrite <- !phi_to_L.
    + intros [L]. exists (fun n => nth (pos.pos2nat n) L 0).
      now rewrite !phi_to_L, !eval_L_from.
Qed.      

Definition test_eq := (fun '(p1,p2,L) => Nat.eqb (eval p1 L) (eval p2 L)).

Instance term_test_eq : computable test_eq.
Proof.
  extract.
Qed.

Definition cons' : nat * list nat -> list nat := fun '(n, L) => n :: L.

Instance term_cons' : computable cons'.
Proof.
  extract.
Qed.

Definition T_list_nat := @L_list nat opt_to_list.

Instance computable_cumul {X} `{registered X} : computable (@cumul X).
Proof.
  extract.
Qed.

Instance term_T_list : computable T_list_nat.
Proof.
  unfold T_list_nat, L_list.
  change (computable
    (fix T_list (n : nat) : list (list nat) :=
       match n with
       | 0 => [[]]
       | S n0 => (T_list n0 ++ map cons' (L_nat n0 × T_list n0))%list
       end)).
  extract.
Qed.
  
Lemma H10_enumerable : L_enumerable (fun '(p1, p2) => exists L, eval p1 L = eval p2 L).
Proof.
  eapply L_enumerable_ext.
  eapply projection with (Y := list nat).
  instantiate (1 := fun '( (p1,p2), L) => eval p1 L = eval p2 L).
  2:{ intros []. firstorder. }
  eapply L_enumerable_enum.
  exists (fix L n := match n with 0 => [] | S n => L n ++ filter test_eq (list_prod (list_prod (L_poly n) (L_poly n)) (T_list_nat  n)) end)%list.
  repeat split.
  - extract.
  - eauto.
  - destruct x as [[p1 p2] L]. intros.
    destruct (enum_poly p1) as [m1], (enum_poly p2) as [m2], (enumerator__T_list opt_to_list _ L) as [m3].
    exists (1 + m1 + m2 + m3). in_app 2.
    fold plus. eapply in_filter_iff. split.
    + rewrite !in_prod_iff. repeat split; eapply cum_ge'; try eassumption; eauto; lia.
    + unfold test_eq. edestruct (Nat.eqb_spec (eval p1 L) (eval p2 L)); eauto.
  - destruct x as [[p1 p2] L]. intros [m].
    induction m.
    + inv H.
    + eapply in_app_iff in H as [|].
      * eauto.
      * eapply in_filter_iff in H as []. unfold test_eq in H0.
        destruct (Nat.eqb_spec (eval p1 L) (eval p2 L)); eauto.
Qed.

Fixpoint poly_eqb p1 p2 :=
  match p1, p2 with
  | poly_cnst n1, poly_cnst n2 => Nat.eqb n1 n2
  | poly_var v1, poly_var v2 => Nat.eqb v1 v2
  | poly_add p1 p2, poly_add p1' p2' => poly_eqb p1 p1' && poly_eqb p2 p2'
  | poly_mul p1 p2, poly_mul p1' p2' => poly_eqb p1 p1' && poly_eqb p2 p2'
  | _,_ => false
  end.

Lemma poly_eqb_spec p1 p2 :
  reflect (p1 = p2) (poly_eqb p1 p2).
Proof.
  revert p2; induction p1; destruct p2; cbn.
  all: try destruct d; try destruct d0; try now (econstructor; congruence).
  - destruct (Nat.eqb_spec n n0); subst; econstructor; congruence.
  - destruct (Nat.eqb_spec n n0); subst; econstructor; congruence.
  - destruct (IHp1_1 p2_1), (IHp1_2 p2_2); cbn; econstructor; congruence.
  - destruct (IHp1_1 p2_1), (IHp1_2 p2_2); cbn; econstructor; congruence.
Qed.

Instance term_poly_beq : computable poly_eqb.
Proof.
  extract.
Qed.

Theorem H10_converges :
  H10 ⪯ converges.
Proof.
  eapply reduces_transitive. eapply red.
  eapply L_enumerable_halt.
  2: eapply H10_enumerable.
  exists (fun '( (p1, p2), (p1', p2')) => poly_eqb p1 p1' && poly_eqb p2 p2'). split.
  - econstructor. extract.
  - intros ( (p1, p2), (p1', p2')).
    destruct (poly_eqb_spec p1 p1'), (poly_eqb_spec p2 p2'); cbn; firstorder congruence.
Qed.
(* Print Assumptions eval_L_from. *)
