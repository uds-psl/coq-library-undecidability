(* Reformulation of single Diophantine equations, i.e. p = q for Diophantine polynomials, without parameters. *)

Inductive dio_op_pfree := do_add_pfree | do_mul_pfree.

(* Syntax without a constructor for parameters, variables fixed to range over nat *)

Inductive dio_polynomial_pfree : Set :=
| dp_nat_pfree : nat -> dio_polynomial_pfree (* natural number constant *)
| dp_var_pfree : nat -> dio_polynomial_pfree (* existentially quantified variable *)
| dp_comp_pfree : dio_op_pfree -> dio_polynomial_pfree -> dio_polynomial_pfree -> dio_polynomial_pfree.

Fixpoint dp_eval_pfree φ p := 
  match p with
  | dp_nat_pfree n => n
  | dp_var_pfree v => φ v
  | dp_comp_pfree do_add_pfree p q => dp_eval_pfree φ p + dp_eval_pfree φ q 
  | dp_comp_pfree do_mul_pfree p q => dp_eval_pfree φ p * dp_eval_pfree φ q 
  end.

Definition H10p_PROBLEM := (dio_polynomial_pfree * dio_polynomial_pfree)%type.
Definition H10p_sem e φ := dp_eval_pfree φ (fst e) = dp_eval_pfree φ (snd e). 
Definition H10p (e : H10p_PROBLEM) := exists φ, H10p_sem e φ.
