Require Import Arith ZArith Lia List.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list gcd prime php utils_nat.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.H10.ArithLibs 
  Require Import Zp lagrange.

From Undecidability.H10 
  Require Import H10.

From Undecidability.H10.Dio 
  Require Import dio_logic dio_elem dio_single.

From Undecidability.H10.ArithLibs 
  Require Import Zp lagrange.

Section diophantine_polynomial.

  Variable (V P : Set).

  Inductive dio_polynomial : Set :=
    | dp_cnst : Z -> dio_polynomial                  (* integer constant *)
    | dp_var : V   -> dio_polynomial                  (* existentially quantified variable *)
    | dp_par : P   -> dio_polynomial                  (* parameter *)
    | dp_comp : dio_op -> dio_polynomial -> dio_polynomial -> dio_polynomial.

  Notation dp_add := (dp_comp do_add).
  Notation dp_mul := (dp_comp do_mul).

  Fixpoint dp_var_list p :=
    match p with
      | dp_cnst _      => nil
      | dp_var v      => v::nil
      | dp_par _      => nil
      | dp_comp _ p q => dp_var_list p ++ dp_var_list q
    end.

  Fixpoint dp_par_list p :=
    match p with
      | dp_cnst _      => nil
      | dp_var _      => nil
      | dp_par x      => x::nil
      | dp_comp _ p q => dp_par_list p ++ dp_par_list q
    end.

  (* ρ σ ν φ *)

  Fixpoint dp_eval φ ν p := 
    match p with
      | dp_cnst n => n
      | dp_var v => φ v
      | dp_par i => ν i
      | dp_comp do_add p q => dp_eval φ ν p + dp_eval φ ν q 
      | dp_comp do_mul p q => dp_eval φ ν p * dp_eval φ ν q 
    end % Z.

  Fact dp_eval_ext φ ν φ' ν' p :
        (forall v, In v (dp_var_list p) -> φ v = φ' v) 
     -> (forall i, In i (dp_par_list p) -> ν i = ν' i) 
     -> dp_eval φ ν p = dp_eval φ' ν' p.
  Proof.
    induction p as [ | | | [] p Hp q Hq ]; simpl; intros H1 H2; f_equal; auto;
      ((apply Hp || apply Hq); intros; [ apply H1 | apply H2 ]; apply in_or_app; auto).
  Qed.

  Fact dp_eval_fix_add φ ν p q : dp_eval φ ν (dp_add p q) = (dp_eval φ ν p + dp_eval φ ν q) % Z.
  Proof. trivial. Qed.

  Fact dp_eval_fix_mul φ ν p q : dp_eval φ ν (dp_mul p q) = (dp_eval φ ν p * dp_eval φ ν q) % Z.
  Proof. trivial. Qed.

  Fixpoint dp_size p :=
    match p with
      | dp_cnst n => 1
      | dp_var v => 1
      | dp_par i => 1
      | dp_comp _ p q => 1 + dp_size p + dp_size q 
    end.

  Fact dp_size_fix_comp o p q : dp_size (dp_comp o p q) = 1 + dp_size p + dp_size q.
  Proof. auto. Qed.

  Definition dio_single := (dio_polynomial * dio_polynomial)%type.
  Definition dio_single_size (e : dio_single) := dp_size (fst e) + dp_size (snd e).

  Definition dio_single_pred e ν := exists φ, dp_eval φ ν (fst e) = dp_eval φ ν (snd e).

End diophantine_polynomial.

Arguments dp_cnst {V P}.
Arguments dp_var {V P}.
Arguments dp_par {V P}.
Arguments dp_comp {V P}.

Notation dp_add := (dp_comp do_add).
Notation dp_mul := (dp_comp do_mul).

Local Definition inj k n := 4 * n + k.

Lemma injection_spec k1 k2 n m : k1 < 4 -> k2 < 4 -> inj k1 n = inj k2 m -> k1 = k2 /\ n = m.
Proof.
  intros. unfold inj in *. lia.
Qed.

Section pos_injs.

  Fixpoint inj0 {n} (p : pos n) : pos (n * 4).
  Proof.
    destruct p.
    - exact pos0.
    - exact (pos_right _ (inj0 _ p)).
  Defined.

  Fixpoint inj1 {n} (p : pos n) : pos (n * 4).
  Proof.
    destruct p.
    - exact pos1.
    - exact (pos_right _ (inj1 _ p)).
  Defined.

  Fixpoint inj2 {n} (p : pos n) : pos (n * 4).
  Proof.
    destruct p.
    - exact pos2.
    - exact (pos_right _ (inj2 _ p)).
  Defined.

  Fixpoint inj3 {n} (p : pos n) : pos (n * 4).
  Proof.
    destruct p.
    - exact pos3.
    - exact (pos_right _ (inj3 _ p)).
  Defined.

End pos_injs.

Module dionat := dio_single.

Notation dp_sq a := (dp_comp do_mul a a).
Notation sq a := (a * a)%Z.

Fixpoint to_Z_poly E n (p : dionat.dio_polynomial (pos n) E) : dio_polynomial (pos (n * 4)) E :=
  match p with
  | dionat.dp_nat n => dp_cnst (Z.of_nat n)
  | dionat.dp_var v => dp_add (dp_sq (dp_var (inj3 v))) (dp_add (dp_sq (dp_var (inj2 v))) (dp_add (dp_sq (dp_var (inj1 v))) (dp_sq (dp_var (inj0 v)))))
  | dionat.dp_par p => dp_par p
  | dionat.dp_comp o p1 p2 => dp_comp o (to_Z_poly p1) (to_Z_poly p2)
  end.

Lemma create_sol_correct E (n : nat) (Φ : pos n -> nat) (Φ' : pos (n * 4) -> Z) :
  (forall i : pos n, Z.of_nat (Φ i) = sq (Φ' (inj3 i)) + sq (Φ' (inj2 i)) + sq (Φ' (inj1 i)) + sq (Φ' (inj0 i)))%Z ->
  forall p : dionat.dio_polynomial (pos n) E, Z.of_nat (dio_single.dp_eval Φ (fun _ : E => 0) p) = dp_eval Φ' (fun _ : E => 0%Z) (to_Z_poly p).
Proof.
  intros H p. 
  induction p as [ k | v | | [] ]; cbn; auto.
  - rewrite H; ring.
  - rewrite Nat2Z.inj_add; congruence.
  - rewrite Nat2Z.inj_mul; congruence.
Qed.

Lemma create_sol_exists (n : nat) (Φ : pos n -> nat) : exists (Φ' : pos (n * 4) -> Z),
    (forall i : pos n, Z.of_nat (Φ i) = sq (Φ' (inj3 i)) + sq (Φ' (inj2 i)) + sq (Φ' (inj1 i)) + sq (Φ' (inj0 i)))%Z.
Proof.
  induction n as [ | n IHn ].
  - exists (fun _ => 0%Z); intros p; invert pos p.
  - destruct (IHn (fun j => Φ (pos_nxt j))) as [Φ' H'].
    cbn [mult].
    destruct (lagrange_theorem_nat (Φ pos0)) as (a & b & c & d & Hl).
    exists (fun j : pos (4 + n * 4) => 
       match pos_both _ _ j with 
        | inl pos0 => a 
        | inl pos1 => b 
        | inl pos2 => c 
        | inl _    => d 
        | inr j => Φ' j 
      end).
    intros p; invert pos p; auto.
    rewrite Hl; ring.
Qed.

Lemma recover_sol_exists (n : nat) (Φ' : pos (n * 4) -> Z) : exists (Φ : pos n -> nat),
    (forall i : pos n, Z.of_nat (Φ i) = sq (Φ' (inj3 i)) + sq (Φ' (inj2 i)) + sq (Φ' (inj1 i)) + sq (Φ' (inj0 i)))%Z.
Proof.
  induction n as [ | n IHn ].
  - exists (fun _ => 0); intros p; invert pos p.
  - destruct (IHn (fun j => Φ' (pos_right 4 j))) as [Φ H].
    unshelve eexists.
    + intros p; invert pos p.
      * exact (Z.to_nat (sq (Φ' (inj3 pos0)) + sq (Φ' (inj2 pos0)) + sq (Φ' (inj1 pos0)) + sq (Φ' (inj0 pos0)))).
      * exact (Φ p).
    + intros p; invert pos p.
      * rewrite Z2Nat.id; auto.
        pose proof (Z.square_nonneg (Φ' pos3)).
        pose proof (Z.square_nonneg (Φ' pos2)).
        pose proof (Z.square_nonneg (Φ' pos1)).
        pose proof (Z.square_nonneg (Φ' pos0)).
        nia.
      * apply H.
Qed.

Lemma create_sol (n : nat) (Φ : pos n -> nat) : exists Φ' : pos (n * 4) -> Z,
  forall p : dionat.dio_polynomial (pos n) (pos 0), Z.of_nat (dio_single.dp_eval Φ (fun _ => 0) p) = dp_eval Φ' (fun _ => 0%Z) (to_Z_poly p).
Proof.
  destruct (create_sol_exists Φ) as [Φ'].
  exists Φ'; intro; now eapply create_sol_correct.
Qed.

Lemma recover_sol (n : nat) (Φ' : pos (n * 4) -> Z) : exists Φ : pos n -> nat,
  forall p : dionat.dio_polynomial (pos n) (pos 0), Z.of_nat (dio_single.dp_eval Φ (fun _ => 0) p) = dp_eval Φ' (fun _ => 0%Z) (to_Z_poly p).
Proof.
  destruct (recover_sol_exists Φ') as [Φ].
  exists Φ; intro; now eapply create_sol_correct.
Qed.

Definition H10Z_PROBLEM := { n : nat & dio_polynomial (pos n) (pos 0) }.

(** The original H10 over relative intergers is P(x1,..,xn) = 0 *)

Definition H10Z : H10Z_PROBLEM -> Prop.
Proof.
  intros (n & p).
  exact (exists Φ, dp_eval Φ (fun _ => 0%Z) p = 0%Z).
Defined.

From Undecidability.Problems 
  Require Import Reduction.

Opaque Zmult.

Lemma H10_H10Z : H10 ⪯ H10Z.
Proof.
  unshelve eexists.
  - intros (n & p & q). 
    exists (n * 4).
    exact (dp_add (to_Z_poly p) (dp_mul (dp_cnst (-1)%Z) (to_Z_poly q))).
  - intros (n & p & q).
    simpl; split; intros [ Φ H ]; simpl in *.
    + destruct (create_sol Φ) as [Φ' H'].
      exists Φ'. 
      rewrite <- !H'; lia.
    + destruct (recover_sol Φ) as [Φ' H'].
      exists Φ'; simpl.
      apply Nat2Z.inj; rewrite !H'; lia.
Qed.

Check H10_H10Z.

