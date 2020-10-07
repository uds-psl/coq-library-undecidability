From Undecidability Require Export UpToC.

Require Import smpl.Smpl.
From Coq Require Import Setoid.
From Coq Require Import CRelationClasses CMorphisms.
From Undecidability Require Export UpToC.
From Undecidability Require Export GenericNary.
From PslBase Require FinTypes.

Local Set Universe Polymorphism. 


Lemma leToC_eta X (f g :X -> _) :
  (leUpToC f g) = (leUpToC (fun x => f x) (fun x => g x)).
Proof. reflexivity. Qed.

Smpl Add 2 rewrite leToC_eta in *: nary_prepare.



Section workaround.
  (*This makes the apply_nary tactic and the rewrites with leToC_eta and "=" work *)
  Local Generalizable Variables A R eqA B S eqB.

  Global Instance pointwise_reflexive {A} `(reflb : Reflexive B eqB) :
    Reflexive (pointwise_relation A eqB) | 9.
  Proof. firstorder. Qed.
  Global Instance pointwise_symmetric {A} `(symb : Symmetric B eqB) :
    Symmetric (pointwise_relation A eqB) | 9.
  Proof. firstorder. Qed.
  Global Instance pointwise_transitive {A} `(transb : Transitive B eqB) :
    Transitive (pointwise_relation A eqB) | 9.
  Proof. firstorder. Qed.
  Global Instance pointwise_equivalence {A} `(eqb : Equivalence B eqB) :
    Equivalence (pointwise_relation A eqB) | 9.
  Proof. firstorder. Qed.


  Instance workaround1 : @subrelation Type (@eq Type) arrow.
  Proof. cbv. firstorder congruence. Qed.
  
  Global Instance workaround2 X Y: (subrelation (pointwise_relation X (@eq Y)) (Morphisms.pointwise_relation X eq)).
  Proof. firstorder. Qed.

End workaround.

Lemma upToC_add_nary (domain : list Set) F (f1 f2 : Rarrow domain nat) :
  Uncurry f1 <=c F
  -> Uncurry f2 <=c F
  -> Fun' (fun x => App f1 x + App f2 x) <=c F.
Proof.
  prove_nary upToC_add.
Qed.


Lemma upToC_max_nary (domain : list Set) F (f1 f2 : Rarrow domain nat) :
  Uncurry f1 <=c F
  -> Uncurry f2 <=c F
  -> Fun' (fun x => max (App f1 x) (App f2 x)) <=c F.
Proof.
  prove_nary upToC_max.
Qed.

Lemma upToC_min_nary (domain : list Set) F (f1 f2 : Rarrow domain nat) :
  Uncurry f1 <=c F
  -> Uncurry f2 <=c F
  -> Fun' (fun x => min (App f1 x) (App f2 x)) <=c F.
Proof.
  prove_nary upToC_min.
Qed.


Lemma upToC_mul_c_l_nary (domain : list Set)c F  (f : Rarrow domain nat):
  Uncurry f <=c F
  -> Fun' (fun x => c * App f x) <=c F.
Proof.
  prove_nary upToC_mul_c_l.
Qed.

Lemma upToC_mul_c_r_nary (domain : list Set)  c F (f : Rarrow domain nat):
  Uncurry f <=c F -> Fun'(fun x => App f x * c) <=c F.
Proof.
  prove_nary upToC_mul_c_r.
Qed.

Lemma upToC_c_nary (domain : list Set) c F:
  (fun _ => 1) <=c F ->  
  Const' domain c <=c F.
Proof.
  prove_nary upToC_c.
Qed.


Lemma upToC_S_nary (domain : list Set) F (f : Rarrow domain nat) :
  Const' domain 1 <=c F
  -> Uncurry f <=c F
  -> Fun' (fun x => S (App f x)) <=c F.
Proof.
  prove_nary upToC_S.
Qed.

Lemma upToC_mul_nary (domain : list Set) (F1 F2 f1 f2 : Rarrow domain nat) :
  Uncurry f1 <=c Uncurry F1
  -> Uncurry f2 <=c Uncurry F2
  -> Fun' (fun x => App f1 x * App f2 x) <=c Fun' (fun x => App F1 x * App F2 x).
Proof.
  prove_nary upToC_mul.
Qed.

Lemma upToC_pow_r_drop_nary domain c f (F : Rarrow domain nat) :
  0 < c
  -> f <=c Uncurry F
  -> f <=c Fun' (fun x => (App F x) ^ c).
  now prove_nary upToC_pow_r_drop.
Qed.

Lemma upToC_pow_le_compat_nary domain c c' (f f' : Rarrow domain nat) :
  0 < c -> c <= c'
  -> Uncurry f <=c Uncurry f'
  -> Fun' (fun x => (App f x) ^ c) <=c Fun' (fun x => (App f' x) ^ c').
  now prove_nary upToC_pow_le_compat.
Qed.    


(** Applying n-ary leUpToC lemmas *)

Ltac domain_of_prod S :=
  let S := constr:(S) in   
  let S := eval simpl in S in
  list_of_tuple S.


Ltac leUpToC_domain G :=
  match G with
  | @leUpToC ?F _ _ =>
    let L := domain_of_prod F in
    let L := constr:(L) in
    exact (Mk_domain_of_goal L)
  end.

Hint Extern 0 Domain_of_goal => (mk_domain_getter leUpToC_domain) : domain_of_goal.






Smpl Add 6 first [nary simple apply upToC_add_nary | nary simple apply upToC_mul_c_l_nary | nary simple apply upToC_mul_c_r_nary
                  | nary simple apply upToC_max_nary| nary simple apply upToC_min_nary
                  | progress (nary simple apply upToC_c_nary) | _applyIfNotConst_nat (nary simple apply upToC_S_nary)] : upToC.


Ltac destruct_pair_rec p :=
  lazymatch type of p with
    (_*_)%type=> let lhs := fresh "p" in
            let x := fresh "x" in
            destruct p as [lhs x];destruct_pair_rec lhs 
  | _ => idtac
  end.

Ltac upToC_le_nary_solve :=
  let x := fresh "x" in
  apply upToC_le;intros x;destruct_pair_rec x; first [nia|lia].

Smpl Add upToC_le_nary_solve : upToC_solve.


Goal
  @leUpToC (nat*bool*nat)
  (fun '(xxx,y,z) => xxx+2+3*z) (fun '(x,y,z) => x+z+1).
  smpl_upToC_solve.
Qed.


Goal (fun '(x,y) => S x + 3 + S y) <=c (fun '(x,y) => x+y+1).
Proof.
  timeout 20 (smpl_upToC_solve).
Qed.



Goal (fun '(x,y) => 3) <=c (fun '(x,y) => x+y+1).
Proof.
  smpl upToC. smpl upToC_solve.
Qed.

Section bla.
  Import FinTypes.
  Lemma leUpToC_finCases_nary domain (Y:FinTypes.finType) Z__case (cases : forall (y:Y), Z__case y -> Rtuple domain) (f : Rarrow domain nat) (F : Rtuple domain -> nat) :
    (forall x, exists y (z : Z__case y), cases y z = x)
    -> (forall y, (fun z => App f (cases y z)) <=c (fun z => F (cases y z)))
    -> Fun' (fun x => App f x) <=c F.
  Proof.
    prove_nary leUpToC_finCases.
  Qed.
End bla.
