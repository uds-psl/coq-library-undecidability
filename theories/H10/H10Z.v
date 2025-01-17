(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             Yannick Forster            [+]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                             [+] Affiliation Saarland Univ. *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import Arith ZArith Lia List.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list gcd prime php utils_nat.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.H10.Dio 
  Require Import dio_logic dio_single.

From Undecidability.H10.ArithLibs 
  Require Import Zp lagrange.

Set Implicit Arguments.

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

Definition H10Z_PROBLEM := { n : nat & dio_polynomial (pos n) (pos 0) }.

(* The original H10 over relative intergers is P(x1,..,xn) = 0 *)

Definition H10Z : H10Z_PROBLEM -> Prop.
Proof.
  intros (n & p).
  exact (exists Φ, dp_eval Φ (fun _ => 0%Z) p = 0%Z).
Defined.
