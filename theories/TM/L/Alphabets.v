From Undecidability Require Import TM.Util.Prelim.
From Undecidability Require Import TM.Code.Code.
From Undecidability Require Import LM_heap_def.

(** * Alphabets *)

Inductive ACom : Type := retAT | lamAT | appAT.

Coercion ACom2Com (a : ACom) : Tok :=
  match a with
  | retAT => retT
  | lamAT => lamT
  | appAT => appT
  end.


Instance ACom_eq_dec : eq_dec ACom.
Proof. intros x y; hnf. decide equality. Defined.

Instance ACom_finType : finTypeC (EqType ACom).
Proof. split with (enum := [retAT; lamAT; appAT]). intros [ | | ]; cbn; reflexivity. Defined.

Instance ACom_inhab : inhabitedC ACom := ltac:(repeat constructor).

Instance Encode_ACom : codable ACom ACom := Encode_Finite (FinType(EqType ACom)).


Coercion Com_to_sum (t : Tok) : (nat + ACom) :=
  match t with
  | varT x => inl x
  | appT => inr appAT
  | lamT => inr lamAT
  | retT => inr retAT
  end.

Definition sigCom := sigSum sigNat ACom.
Definition sigCom_fin := FinType (EqType sigCom).

Instance Encode_Com : codable sigCom Tok :=
  {|
    encode x := encode (Com_to_sum x)
  |}.

Definition Encode_Com_size (t : Tok) : nat :=
  size (Com_to_sum t).

Lemma Encode_Com_hasSize (t : Tok) :
  size t = Encode_Com_size t.
Proof. reflexivity. Qed.


Definition sigHAdd := sigNat.
Definition sigHAdd_fin := FinType(EqType sigHAdd).

Definition sigPro := sigList sigCom.
Instance Encode_Prog : codable sigPro Pro := _.
Definition sigPro_fin := FinType(EqType sigPro).

Definition sigHClos := sigPair sigHAdd sigPro.
Definition sigHClos_fin := FinType(EqType sigHClos).
Instance Encode_HClos : codable sigHClos HClos := _.

Definition sigHEntr' := sigPair sigHClos sigHAdd.
Instance Encode_HEntr' : codable (sigHEntr') (HClos*HAdd) := _.
Definition sigHEntr'_fin := FinType(EqType sigHEntr').

Definition sigHEntr := sigOption sigHEntr'.
Instance Encode_HEntr : codable (sigHEntr) HEntr := _.
Definition sigHEntr_fin := FinType(EqType sigHEntr).

Definition sigHeap := sigList sigHEntr.
Instance Encode_Heap : codable (sigHeap) Heap := _.
Definition sigHeap_fin := FinType(EqType sigHeap).
