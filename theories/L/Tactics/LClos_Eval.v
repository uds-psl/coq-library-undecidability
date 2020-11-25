From Undecidability.L.Tactics Require Export LClos.
Require Import FunInd. 
Open Scope LClos.

(* *** Closure calculus interpreter *)

Definition CompBeta s t :=
  match s,t with
    |CompClos (lam ls) A,CompClos (lam lt) B => Some (CompClos ls (CompClos (lam lt) B::A))
    |_,_ => None
  end.

Definition CompAppCount j u v :=
  match u,v with
    (l,u),(k,v) => (j+(l+k),CompApp u v)
  end.

Fixpoint CompSeval n (u: nat * Comp) : nat * Comp:=
  match n with
      S n =>
      match u with
        | (l,CompApp s t) =>
          match CompBeta s t with
            | Some u => CompSeval n (S l,u)
            | None => CompSeval n (CompAppCount l (CompSeval n (0,s)) (CompSeval n (0,t)))
          end
        | (l,CompClos (app s t) A) => CompSeval n (l,(CompClos s A) (CompClos t A))
        | (l,CompClos (var x) A) => (l,nth x A (CompVar x))
        | u => u 
      end
    | _ => u
  end.

Lemma CompBeta_validComp s t u: validComp s -> validComp t -> CompBeta s t = Some u -> validComp u.
Proof with repeat (auto || congruence || subst || simpl in * || intuition).
  intros vs vt eq. inv vs; inv vt... destruct s0... destruct s,s0... inv eq. repeat constructor... inv H1...
Qed.
(*
Lemma CompBeta_lamComp s t u: CompBeta s t = Some u -> (lamComp s /\ lamComp t).
Proof with repeat (auto || congruence || subst || simpl in.
  unfold CompBeta. intros equ. destruct s,t... destruct s... destruct s... destruct s,s0...
Qed.

Lemma CompBeta_lamComp2 s t: CompBeta s t = None -> (~lamComp s \/ ~lamComp t).
Proof with repeat inv_validComp;try (intros ?;repeat inv_validComp).
  unfold CompBeta. intros equ. destruct s,t;try now left... right... destruct s. left... left... destruct s0... right... right... congruence.
Qed.
*)
Lemma CompSeval_validComp s k n: validComp s -> validComp (snd (CompSeval n (k,s))).
Proof with repeat (apply validCompApp ||apply validCompClos || eauto || congruence || subst || simpl in * || intuition). 
  revert s k. induction n; intros s k vs... inv vs...
  case_eq (CompBeta s0 t);intros...
  -apply CompBeta_validComp in H1...
  -assert (IHn1 := IHn s0 0 H). assert (IHn2 := IHn t 0 H0).
   unfold snd in *. do 2 destruct ((CompSeval n (_,_)))...
  -destruct s0...
Qed.

Hint Resolve CompSeval_validComp : core.

Lemma CompBeta_sound s t u: CompBeta s t = Some u -> s t >[(1)] u.
Proof with repeat (auto || congruence || subst || simpl in * || intuition).
  intros eq. destruct s,t... destruct s... destruct s... destruct s... destruct s0... inv eq. repeat constructor...
Qed.

Functional Scheme CompSeval_ind := Induction for CompSeval Sort Prop.

Lemma CompSeval_sound' n s l : let (k,t) := CompSeval n (l,s) in k >= l /\ s >[(k-l)] t.
Proof with (repeat inv_validComp;repeat (constructor || intuition|| subst ; eauto using star || rewrite Nat.sub_diag||cbn in *)).
  pose (p:= (l,s)).
  change (let (k, t) := CompSeval n p in k >= fst p /\ (snd p) >[(k-(fst p))] t).
  generalize p. clear l s p. intros p. 
  functional induction (CompSeval n p); intros;cbn...
  -apply CompBeta_sound in e2. destruct (CompSeval _ _);split... eapply CPow_trans;try  eassumption. lia.
  -repeat destruct (CompSeval _ _)... eapply CPow_trans...
  -repeat destruct (CompSeval _ _)... eapply CPow_trans...
Qed.

Lemma CompSeval_sound (n k:nat) s t : CompSeval n (0,s) = (k,t) -> s >[(k)] t.
Proof.
  specialize (CompSeval_sound' n s 0). destruct _;intros.
  inv H0. rewrite <- minus_n_O in H. tauto.
Qed.
