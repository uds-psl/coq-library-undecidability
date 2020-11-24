(** * Halting problem for simple binary single-tape Turing machines HaltSBTM *)

Require Import List Bool Nat.
Require Coq.Vectors.Fin.
Import ListNotations.

Definition tape : Type := list bool * option bool * list bool.

Definition left '( (ls, m, rs) : tape) : list bool := ls.

Definition right '((ls, m, rs) : tape) := rs.

Definition curr '((ls, m, rs) : tape) := m.

Definition wr (o : option bool) (t : tape) := 
  match o with
  | Some c => (left t, Some c, right t)
  | None => t
  end.
  
Inductive move : Type := 
    | Lmove : move 
    | Rmove : move 
    | Nmove : move.

Definition mv (m : move) (t : tape) :=
  match m with
  | Lmove => match left t, curr t with
             | l :: ls, None => (ls, Some l, right t)
             | l :: ls, Some c => (ls, Some l, c :: right t)
             | [], Some c => ([], None, c :: right t)
             | _, _ => t
             end
  | Rmove => match curr t, right t with
             | None, r :: rs => (left t, Some r, rs) 
             | Some c, r :: rs => (c :: left t, Some r, rs)
             | Some c, [] => (c :: left t, None, [])
             | _ , _ => t
             end
  | Nmove => t
  end.

Record SBTM :=  { num_states : nat ; trans : Fin.t (S num_states) * option bool -> option (Fin.t (S num_states) * option bool * move)}.

Notation state M := (Fin.t (S (num_states M))).

Inductive eval (M : SBTM) : state M -> tape -> state M -> tape -> Prop :=
| eval_halt q t :
    trans M (q, (curr t)) = None ->
    eval M q t q t
| eval_step q t q' w m  q'' t' :
    trans M (q, curr t) = Some (q', w, m) ->
    eval M q' (mv m (wr w t)) q'' t' ->
    eval M q t q'' t'.

Definition HaltSBTM '( (M, t) : SBTM * tape) :=
  exists q' t', eval M (Fin.F1) t q' t'.

Definition HaltSBTMu : { M : SBTM & {q : state M | forall c, trans M (q,c) = None /\ forall q', trans M (q',c) = None -> q' = q }} * tape -> Prop := fun '((existT _ M (exist _ q H)), t) => exists t', eval M Fin.F1 t q t'.
