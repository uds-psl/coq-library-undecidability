From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L Require Import Functions.EqBool.
From Undecidability.L.Datatypes Require Import LBool LNat LOptions LProd.
From Undecidability.L Require Import UpToC.
Require Export List PslBase.Lists.Filter Datatypes.

(** ** Encoding of lists *)

Section Fix_X.
  Variable (X:Type).
  Context {intX : registered X}.
  Import GenEncode.
  Run TemplateProgram (tmGenEncode "list_enc" (list X)).  
  Hint Resolve list_enc_correct : Lrewrite.
  
  (* now we must register the non-constant constructors*)
  
  Global Instance termT_cons : computableTime' (@cons X) (fun a aT => (1,fun A AT => (1,tt))).
  Proof using intX.
    extract constructor.
    solverec.
  Qed.

  (* Lemma list_enc_correct (A:list X) (s t:term): proc s -> proc t -> enc A s t >(2) match A with nil => s | cons a A' => t (enc a) (enc (A')) end. *)
  (* Proof. *)
  (*   extract match.  *)
  (* Qed. *)
  

  Global Instance termT_append : computableTime' (@List.app X) (fun A _ => (5,fun B _ => (length A * 16 +4,tt))).
  Proof using intX.
    extract.
    solverec.
  Qed.

  Global Instance term_filter: computableTime' (@filter X) (fun p pT => (1,fun l _ => (fold_right (fun x res => 16 + res + fst (pT x tt)) 8 l ,tt))).
  Proof using intX.
    change (filter (A:=X)) with ((fun (f : X -> bool) =>
                                    fix filter (l : list X) : list X := match l with
                                                                        | [] => []
                                                                        | x :: l0 => (fun r => if f x then x :: r else r) (filter l0)
                                                                        end)).
    extract.
    solverec.
  Defined.

  Global Instance term_filter_notime: computable (@filter X).
  Proof using intX.
  pose (t:= extT (@filter X)). hnf in t. 
    computable using t.
  Defined.

  Global Instance term_nth : computableTime' (@nth X) (fun n _ => (5,fun l lT => (1,fun d _ => (n*20+9,tt)))). 
  Proof using intX.
    extract.
    solverec.
  Qed.

  Fixpoint inb eqb (x:X) (A: list X) :=
    match A with
      nil => false
    | a::A' => orb (eqb a x) (inb eqb x A')
    end.

  Variable X_eqb : X -> X -> bool.
  Hypothesis X_eqb_spec : (forall (x y:X), Bool.reflect (x=y) (X_eqb x y)).

  Lemma inb_spec: forall x A, Bool.reflect (In x A) (inb X_eqb x A).
  Proof using X_eqb_spec.
    intros x A. induction A.
    -constructor. tauto.
    -simpl. destruct (X_eqb_spec a x).
     +constructor. tauto.
     +inv IHA. destruct (X_eqb_spec a x).
      *constructor. tauto.
      *constructor. tauto.
      *constructor. tauto.
  Qed.

  Global Instance term_inb: computableTime' inb (fun eq eqT => (5,fun x _ => (1,fun l _ =>
                                        (fold_right (fun x' res => callTime2 eqT x' x
                                                                + res + 17) 4 l ,tt)))).
  Proof.
    extract.
    solverec. 
  Defined.

  Global Instance term_inb_notime: computable inb.
  Proof.
    extract.
  Defined.

  Definition pos_nondec  :=
    fix pos_nondec (eqb: X -> X -> bool) (s : X) (A : list X) {struct A} : option nat :=
      match A with
      | [] => None
      | a :: A0 =>
        if eqb s a
        then Some 0
        else match pos_nondec eqb s A0 with
             | Some n => Some (S n)
             | None => None
             end
      end.

  Lemma pos_nondec_spec (x:X) `{eq_dec X} A: pos_nondec X_eqb x A = pos x A.
  Proof using X_eqb_spec.
    induction A;[reflexivity|];cbn.
    rewrite IHA. destruct (X_eqb_spec x a); repeat (destruct _; try congruence).
  Defined.

  Global Instance term_pos_nondec:
    computable pos_nondec.
  Proof.
    extract.
  Defined.

End Fix_X.

Hint Resolve list_enc_correct : Lrewrite.

Fixpoint map_time {X} (fT:X -> nat) xs :=
  match xs with
    [] => 8
  | x :: xs => fT x + map_time fT xs + 12
  end.
  
Instance term_map (X Y:Type) (Hx : registered X) (Hy:registered Y): computableTime' (@map X Y) (fun _ fT => (1,fun l _ => (map_time (fun x => fst (fT x tt)) l,tt))).
Proof.
  extract.
  solverec.
Defined.

Lemma map_time_const {X} c (xs:list X):
  map_time (fun _ => c) xs = length xs * (c + 12) + 8.
Proof.
  induction xs;cbn. all:lia.
Qed.

Lemma mapTime_upTo X (t__f : X -> nat):
  map_time t__f <=c (fun l => length l + sumn (map t__f l) + 1 ).
Proof.
  unfold map_time. exists 12.
  induction x;cbn - [plus mult]. all: nia.
Qed.

Instance term_map_noTime (X Y:Type) (Hx : registered X) (Hy:registered Y): computable (@map X Y).
Proof.
  extract.
Defined.


Instance termT_nth_error (X:Type) (Hx : registered X): computableTime' (@nth_error X) (fun A _ => (5,fun n _ => (min n (length A)*15 + 10,tt))).
Proof.
  extract. solverec.
Qed.

Instance termT_length X `{registered X} : computableTime' (@length X) (fun A _ => ((length A)*11+8,tt)).
extract. solverec.
Qed.

Instance termT_rev_append X `{registered X}: computableTime' (@rev_append X) (fun l _ => (5,fun res _ => (length l*13+4,tt))).
extract.
recRel_prettify.
solverec.
Qed.

Instance termT_rev X `{registered X}: computableTime' (@rev X) (fun l _ => (length l*13+10,tt)).
eapply computableTimeExt with (x:= fun l => rev_append l []).
{intro. rewrite rev_alt. reflexivity. }
extract. solverec.
Qed.

(* Instance not neccessary as alias for nth_error *)
Lemma term_elAt (X:Type) (Hx : registered X) : computable (@elAt X).
Proof.
  exact _.
Abort.

Section list_eqb.

  Variable X : Type.
  Variable eqb : X -> X -> bool.
  Variable spec : forall x y, reflect (x = y) (eqb x y).

  Fixpoint list_eqb A B :=
    match A,B with
    | nil,nil => true
    | a::A',b::B' => eqb a b && list_eqb A' B'
    | _,_ => false
    end.

  Lemma list_eqb_spec A B : reflect (A = B) (list_eqb A B).
  Proof.
    revert B; induction A; intros; destruct B; cbn in *; try now econstructor.
    destruct (spec a x), (IHA B); cbn; econstructor; congruence.
  Qed.

End list_eqb.
Section int.

  Context {X : Type}.
  Context {HX : registered X}.

  Fixpoint list_eqbTime (eqbT: timeComplexity (X -> X -> bool)) (A B:list X) :=
    match A,B with
      a::A,b::B => callTime2 eqbT a b + 22 + list_eqbTime eqbT A B
    | _,_ => 9
    end.
  
  Global Instance term_list_eqb : computableTime' (list_eqb (X:=X))
                                                   (fun _ eqbT => (1,(fun A _ => (5,fun B _ => (list_eqbTime eqbT A B,tt))))).
  Proof.
    extract.
    solverec.                                                                                             
  Defined.

  Definition list_eqbTime_leq (eqbT: timeComplexity (X -> X -> bool)) (A B:list X) k:
    (forall a b, callTime2 eqbT a b <= k)
    -> list_eqbTime eqbT A B <= length A * (k+22) + 9.
  Proof.
    intros H'. induction A in B|-*.
    -cbn. omega.
    -destruct B.
     {cbn. intuition. }
     cbn - [callTime2]. setoid_rewrite IHA.
     rewrite H'. ring_simplify. intuition.
  Qed.

  
  Lemma list_eqbTime_bound_r (eqbT : timeComplexity (X -> X -> bool)) (A B : list X) f:
    (forall (x y:X), callTime2 eqbT x y <= f y) ->
    list_eqbTime eqbT A B <= sumn (map f B) + 9 + length B * 22.
  Proof.
    intros H.
    induction A in B|-*;unfold list_eqbTime;fold list_eqbTime. now Lia.lia.
    destruct B.
    -cbn. Lia.lia.
    -rewrite H,IHA. cbn [length map sumn]. Lia.lia.
  Qed.

  Global Instance eqbList f `{eqbClass (X:=X) f}:
    eqbClass (list_eqb f).
  Proof.
    intros ? ?. eapply list_eqb_spec. all:eauto using eqb_spec.
  Qed.
  Import EqBool.
  Global Instance eqbComp_List `{eqbCompT X (R:=HX)}:
    eqbCompT (list X).
  Proof.
    evar (c:nat). exists c. unfold list_eqb. 
    unfold enc;cbn.
    change (eqb0) with (eqb (X:=X)).
    extract. unfold eqb,eqbTime. fold @enc.
    recRel_prettify2. easy.
    [c]:exact (c__eqbComp X + 6).
    all:unfold c. all:cbn iota beta delta [list_enc].
    all:  change ((match HX with
                   | @mk_registered _ enc _ _ => enc
                   end)) with (enc (X:=X)).
    all:cbn [size]. all: nia.
  Qed.
  
End int.


Instance term_length X {H:registered X}:
  computableTime' (@length X) (fun t _ => (length t * 11 + 8,tt)).  
extract. solverec.
Proof.
Qed.


Fixpoint forallb_time {X} (fT:X -> nat) xs :=
  match xs with
    [] => 8
  | x :: xs => fT x + forallb_time fT xs + 15
  end.

Lemma forallb_time_eq X f (l:list X):
  forallb_time f l = sumn (map f l) + length l * 15 + 8.
Proof.
  induction l;cbn;nia.
Qed.

Lemma forallb_time_const X c (l:list X):
  forallb_time (fun _ =>  c) l = length l * (c+15) + 8.
Proof.
  induction l;cbn;nia.
Qed.

Instance term_forallb X {HX:registered X}:
  computableTime' (@forallb X) (fun f t__f => (1,fun l _ => (forallb_time (fun x => fst (t__f x tt)) l,tt))).
Proof.
  extract.
  solverec.
Qed.


Section list_prod.

  Context {X Y : Type}.
  Context {HX : registered X} {HY : registered Y}.
  
  Global Instance term_list_prod : computable (@list_prod X Y).
  Proof.
    unfold list_prod.
    change (computable
              (fix list_prod (l : list X) (l' : list Y) {struct l} : list (X * Y) :=
                 match l with
                 | [] => []
                 | x :: t => map (pair x) l' ++ list_prod t l'
                 end)).
    extract.
  Qed.

End list_prod.


Lemma size_list X `{registered X} (l:list X):
  size (enc l) = sumn (map (fun x => size (enc x) + 5) l)+ 4.
Proof.
  change (enc l) with (list_enc l).
  induction l.
  -easy.
  -cbn [list_enc map sumn size].
   change ((match H with
            | @mk_registered _ enc _ _ => enc
            end a)) with (enc a). solverec. 
Qed.

Lemma size_list_cons (X : Type) (H : registered X) x (l : list X):
  size (enc (x::l)) = size (enc x) + size (enc l) + 5.
Proof.
  rewrite !size_list. cbn. lia.
Qed.

Lemma size_list_enc_r {X} `{registered X} (l:list X):
  length l <= size (enc l).
Proof.
  rewrite size_list. induction l;cbn. all:lia.
Qed.

Instance term_repeat A `{registered A}: computableTime' (@repeat A) (fun _ _ => (5, fun n _ => (n * 12 + 4,tt))).
Proof.
  extract. solverec.
Qed.


(*MOVE*)
Definition lengthEq A :=
  fix f (t:list A) n :=
    match n,t with
      0,nil => true
    | (S n), _::t => f t n
    | _,_ => false
    end.
Lemma lengthEq_spec A (t:list A) n:
| t | =? n = lengthEq t n.
Proof.
  induction n in t|-*;destruct t;now cbn.
Qed.
Definition lengthEq_time k := k * 15 + 9.
Instance term_lengthEq A `{registered A} : computableTime' (lengthEq (A:=A)) (fun l _ => (5, fun n _ => (lengthEq_time (min (length l) n),tt))).
Proof.
  extract. unfold lengthEq_time. solverec.
Qed.


Section concat.
  Context X `{registered X}.

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

  
  Lemma _term_rev_concat :
    { time : UpToC (fun l => sumn (map (@length _) l) + length l + 1) &
             computableTime' (@rev_concat) (fun _ _ => (5,fun l _ => (time l,tt)))}.
  Proof.      
    evar (c1 : nat).
    exists_UpToC (fun l => c1 * (sumn (map (@length _) l) + length l + 1) ).
    { extract. recRel_prettify2.
      all:cbn - [plus mult].
      all:enough (c1>=20) by nia.
      instantiate (c1:=20). all:subst c1;nia. 
    }
    smpl_upToC_solve.
  Qed.
  Global Instance term_rev_concat : computableTime' rev_concat _ := projT2 _term_rev_concat.

  
  Lemma _term_concat :
    { time : UpToC (fun l => sumn (map (@length _) l) + length l + 1) &
             computableTime' (@concat X) (fun l _ => (time l,tt))}.
  Proof.
    eexists_UpToC time. [time]: intros x.
    eapply computableTimeExt with (x := fun l => rev (rev_concat [] l)).
    -intros l;hnf. rewrite rev_concat_rev. easy.
    -extract. solverec. unfold time. reflexivity.
    -unfold time. setoid_rewrite rev_concat_length. setoid_rewrite length_concat. smpl_upToC_solve.
  Qed.

  Global Instance term_concat : computableTime' (@concat X) _ := projT2 _term_concat.
End concat.
