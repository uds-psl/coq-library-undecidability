From Undecidability.L Require Import Tactics.LTactics Datatypes.LNat Datatypes.LTerm.

Class decodable X `{registered X}: Type :=
  {
    decode : term -> option X;
    decode_correct : forall (x:X), decode (enc x) = Some x;
    decode_correct2 : forall (t : term) (x : X), decode t = Some x -> enc x = t
  }.

Arguments decodable : clear implicits.
Arguments decode    : clear implicits.

Arguments decodable _ {_}.
Arguments decode _ {_} {_} _ : simpl never.



Instance decode_nat : decodable nat.
Proof.
  exists nat_unenc. all:eauto using LNat.unenc_correct, LNat.unenc_correct2.
Defined.


Fixpoint term_decode (s : term) :=
  match s with
  | lam (lam (lam (app 2 n))) =>
    match decode nat n with
      Some n => Some (var n)
    | _ => None
    end
  |  lam (lam (lam (app (app 1 s1) s2))) =>
     match term_decode s1,term_decode s2 with
       Some s1, Some s2 => Some (s1 s2)
     | _,_ => None
     end
  | lam (lam (lam (app O s))) =>
    match term_decode s with
      Some s => Some (lam s)
    | _ => None  end
  | _ => None
  end.

Instance decode_term : decodable term.
Proof.
  exists term_decode.
  all:unfold enc at 1. all:cbn.
  -induction x;cbn. change nat_enc with (enc (X:=nat)).
   +rewrite (decode_correct n). congruence.
   +now rewrite IHx1,IHx2.
   +now rewrite IHx.  all:eauto using LNat.unenc_correct, LNat.unenc_correct2.
  -apply (size_induction (f := size) (p := (fun t => forall x, term_decode t = Some x -> term_enc x = t))). intros t IHt s.
   destruct t eqn:eq. all:cbn.
   all:repeat let eq := fresh in destruct _ eqn:eq. all:try congruence.
   all:intros [= <-].
   +cbn. erewrite IHt.
    *reflexivity.
    *cbn;lia.
    *easy.
   +cbn. change nat_enc with (enc (X:=nat)).
    erewrite decode_correct2. 2:eassumption.  reflexivity.
   +cbn. erewrite !IHt. reflexivity.
    1,3:cbn;lia.
    all:eassumption.
Defined.

From Undecidability.L Require Import Datatypes.Lists.

Definition list_decode X `{decodable X} :=
  fix list_decode (s : term) : option (list X) :=
    match s with
    | lam (lam 1) => Some []
    | lam (lam (app (app O x) xs)) =>
      match decode X x,list_decode xs with
        Some x, Some xs => Some (x::xs)
      | _,_ => None
      end
    | _ => None
    end.

Arguments list_decode : clear implicits.
Arguments list_decode _ {_ _} _.

Instance decode_list X `{registered X} {H:decodable X}: decodable (list X).
Proof.
  exists (list_decode X).
  all:unfold enc at 1. all:cbn.
  -induction x;cbn.
   +easy.
   +setoid_rewrite decode_correct. now rewrite IHx.
  -apply (size_induction (f := size) (p := (fun t => forall x, list_decode X t = Some x -> list_enc x = t))). intros t IHt s.
   destruct t eqn:eq. all:cbn.
   all:repeat let eq := fresh in destruct _ eqn:eq. all:try congruence.
   all:intros [= <-].
   +easy.
   +cbn. change (match H with
                | @mk_registered _ enc _ _ => enc
                 end x) with (enc x). erewrite decode_correct2. 2:easy.
    erewrite IHt.
    *reflexivity.
    *cbn;lia.
    *easy.
Defined.


From Undecidability.L Require Import Datatypes.LProd.

Definition prod_decode X Y `{decodable X} `{decodable Y} (s : term) : option (X*Y) :=
    match s with
    | lam (app (app 0 x) y) =>
      match decode X x,decode Y y with
        Some x, Some y => Some (x,y)
      | _,_ => None                
      end
    | _ => None
    end.

Arguments prod_decode : clear implicits.
Arguments prod_decode _ _ {_ _ _ _}.

Instance decode_prod X Y `{decodable X} `{decodable Y}: decodable (X*Y).
Proof.
  exists (prod_decode X Y).
  all:unfold enc at 1. all:cbn.
  -intros [];cbn.
   +repeat setoid_rewrite decode_correct. easy.
  -destruct t eqn:eq. all:cbn.
   all:repeat let eq := fresh in destruct _ eqn:eq. all:try congruence.
   all:intros ? [= <-]. cbn.
   setoid_rewrite decode_correct2;[|eassumption..]. easy.
Defined.

From Undecidability.L Require Import Datatypes.LOptions.

Definition option_decode X `{decodable X} (s : term) : option (option X) :=
  match s with
  | lam (lam (app 1 x)) => 
    match decode X x with
      Some x => Some (Some x)
    | _ => None
    end
  | lam (lam 0) => Some None
  | _ => None
  end.

Arguments option_decode : clear implicits.
Arguments option_decode _ {_ _} _.

Instance decode_option X `{registered X} {H:decodable X}: decodable (option X).
Proof.
  exists (option_decode X).
  all:unfold enc at 1. all:cbn.
  -intros[];cbn. 2:easy. setoid_rewrite decode_correct. easy. 
  -destruct t eqn:eq. all:cbn.
   all:repeat let eq := fresh in destruct _ eqn:eq. all:try congruence.
   all:intros ? [= <-]. 
   +easy.
   +cbn. change (match H with
                | @mk_registered _ enc _ _ => enc
                 end x) with (enc x). erewrite decode_correct2. all:easy.
Defined.

From Undecidability.L Require Import Datatypes.LBool.


Definition bool_decode (s : term) : option bool:=
  match s with
  | lam (lam 1) => Some true
  | lam (lam 0) => Some false
  | _ => None
  end.

Instance decode_bool: decodable (bool).
Proof.
  exists (bool_decode).
  all:unfold enc at 1. all:cbn.
  -intros[];cbn. all:easy. 
  -destruct t eqn:eq. all:cbn.
   all:repeat let eq := fresh in destruct _ eqn:eq. all:try congruence.
   all:intros ? [= <-]. all:easy.
Defined.
