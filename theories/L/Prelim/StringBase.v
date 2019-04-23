Require Import PslBase.Base Ascii.
Require Export String.

Fixpoint to_string (l : list ascii) :=
  match l with
  | nil => EmptyString
  | x :: xs => String x (to_string xs)
  end.

Fixpoint to_list (s : string) :=
  match s with
  | EmptyString => nil
  | String x xs => x :: (to_list xs)
  end.

Definition rev_string str := (to_string (rev (to_list str))).

Fixpoint name_after_dot' (s : string) (r : string) :=
  match s with
  | EmptyString => r
  | String "#" xs => name_after_dot' xs xs (* see Coq_name in a section *)
  | String "." xs => name_after_dot' xs xs
  | String _ xs => name_after_dot' xs r
  end.

Definition name_after_dot s := name_after_dot' s s.
