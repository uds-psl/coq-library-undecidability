From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Export List.List_enc LBool LNat.
From Undecidability.Shared.Libs.PSL.Lists Require Export Filter.

Definition c__app := 16.
#[global]
Instance termT_append X {intX : encodable X} : computableTime' (@List.app X) (fun A _ => (5,fun B _ => (length A * c__app + c__app,tt))).
Proof.
  extract.
  solverec. all: now unfold c__app. 
Qed.

Definition c__map := 12. 
Fixpoint map_time {X} (fT:X -> nat) xs :=
  match xs with
    [] => c__map
  | x :: xs => fT x + map_time fT xs + c__map
  end.
  
#[global]
Instance term_map (X Y:Type) (Hx : encodable X) (Hy:encodable Y): computableTime' (@map X Y) (fun _ fT => (1,fun l _ => (map_time (fun x => fst (fT x tt)) l,tt))).
Proof.
  extract.
  solverec. all: unfold c__map; solverec. 
Defined. (*because other extract*)


Lemma map_time_const {X} c (xs:list X):
  map_time (fun _ => c) xs = length xs * (c + c__map) + c__map.
Proof.
  induction xs;cbn. all:lia.
Qed.

#[global]
Instance term_map_noTime (X Y:Type) (Hx : encodable X) (Hy:encodable Y): computable (@map X Y).
Proof.
  extract.
Defined. (*because other extract*)
  

#[global]
Instance termT_rev_append X `{encodable X}: computableTime' (@rev_append X) (fun l _ => (5,fun res _ => (length l*13+4,tt))).
extract.
recRel_prettify.
solverec.
Qed.

Definition c__rev := 13.
#[global]
Instance termT_rev X `{encodable X}: computableTime' (@rev X) (fun l _ => ((length l + 1) *c__rev,tt)).
eapply computableTimeExt with (x:= fun l => rev_append l []).
{intro. rewrite rev_alt. reflexivity. }
extract. solverec. unfold c__rev; solverec. 
Qed.

Section Fix_X.
  Variable (X:Type).
  Context {intX : encodable X}.

  Global Instance term_filter: computableTime' (@filter X) (fun p pT => (1,fun l _ => (fold_right (fun x res => 16 + res + fst (pT x tt)) 8 l ,tt))).
  Proof using intX.
    change (filter (A:=X)) with ((fun (f : X -> bool) =>
                                    fix filter (l : list X) : list X := match l with
                                                                        | [] => []
                                                                        | x :: l0 => (fun r => if f x then x :: r else r) (filter l0)
                                                                        end)).
    extract.
    solverec. 
  Defined. (*because other extract*)

  Global Instance term_filter_notime: computable (@filter X).
  Proof using intX.
  pose (t:= extT (@filter X)). hnf in t. 
    computable using t.
  Defined. (*because other extract*)

  Global Instance term_repeat: computable (@repeat X).
  Proof using intX.
    extract.
  Qed.
  
End Fix_X.


Section concat.
  Context X `{encodable X}.

  Fixpoint rev_concat acc (xs : list (list X)) :=
    match xs with
      [] => acc
    | x::xs => rev_concat (rev_append x acc) xs
    end.

  Lemma rev_concat_rev xs acc:
    rev (rev_concat acc xs) = rev acc ++ concat xs.
  Proof.
    induction xs in acc|-*. all:cbn. 2:rewrite IHxs,rev_append_rev. all:autorewrite with list in *. all:easy.
  Qed.

  Lemma rev_concat_length xs acc:
    length (rev_concat acc xs) = length acc + length (concat xs).
  Proof.
    specialize (rev_concat_rev xs acc) as H1%(f_equal (@length _)).
    autorewrite with list in H1. nia.
  Qed.

End concat.
