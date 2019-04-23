From Undecidability.L Require Export Computability.Decidability Datatypes.LNat L.

(** ** Decidabiity of closedness, boundedness and procness *)

Fixpoint boundb (k : nat) (t : term) : bool :=
match t with
| var n => negb (k <=? n)
| app s t => andb (boundb k s) (boundb k t)
| lam s => boundb (S k) s
end.

Instance term_boundb : computable boundb.
Proof.
  extract.
Defined.

Lemma boundb_spec k t : Bool.reflect (bound k t) (boundb k t).
Proof.
  revert k. induction t;intros;cbn. simpl.  
  -destruct (Nat.leb_spec0 k n); simpl;constructor.  intros H. inv H. omega. constructor. omega.
  -specialize (IHt1 k). specialize (IHt2 k). inv IHt1;simpl.
   +inv IHt2;constructor.
    *now constructor.
    *intros C. now inv C.
   +constructor. intros C. now inv C.
  -specialize (IHt (S k)). inv IHt;constructor.
   +now constructor.
   +intros C. now inv C.
Qed.

Definition closedb := boundb 0.

Lemma closedb_spec s : Bool.reflect (closed s) (closedb s).
  unfold closedb.
  destruct (boundb_spec 0 s);constructor; rewrite closed_dcl;auto.
Qed.

Instance term_closedb : computable closedb.
Proof.
  exact _.
Defined.


Fixpoint lambdab (t : term) : bool :=
match t with
| lam _ => true
| _ => false
end.

Instance term_lambdab : computable lambdab.
Proof.
  extract.
Defined.

Lemma lambdab_spec t : Bool.reflect (lambda t) (lambdab t).
Proof.
  destruct t;constructor;[intros H;inv H;congruence..|auto]. 
Qed.

Lemma ldec_lambda : ldec lambda.
Proof.
  apply (dec_ldec lambdab). apply lambdab_spec. 
Qed.

Lemma ldec_closed : ldec closed.
Proof.
  apply (dec_ldec closedb). apply closedb_spec. 
Qed.

Lemma ldec_proc : ldec proc.
Proof.
  apply ldec_conj. apply ldec_closed. apply ldec_lambda.
Qed.
