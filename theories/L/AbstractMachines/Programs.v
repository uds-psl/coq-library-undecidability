From Undecidability.L Require Import Prelim.MoreBase L.

(** * Abstract L machines *)
(** ** Encoding Terms as Programs *)

Inductive Tok := varT (n :nat) | appT | lamT | retT.
Notation Pro := (list Tok) (only parsing).

Instance Tok_eq_dec : eq_dec Tok.
repeat intro. hnf. repeat decide equality.
Qed.

Fixpoint compile (s: L.term) : Pro :=
  match s with
    var x => [varT x]
  | app s t => compile s ++ compile t ++ [appT]
  | lam s => lamT :: compile s ++ [retT]
  end.

Inductive reprP : Pro -> term -> Prop :=
  reprPC s : reprP (compile s) (lam s).

(** *** Program size *)

Definition sizeT t := 
  match t with
    varT n => 1 + n
  |  _ => 1
  end.  

Definition sizeP (P:Pro) := sumn (map sizeT P) + 1.
Hint Unfold sizeP.


Lemma size_geq_1 s: 1<= size s.
Proof.
  induction s;cbn. all:try omega.
Qed.

Lemma sizeP_size' s :size s <= sumn (map sizeT (compile s)).
Proof.
  induction s;cbn.
  all:autorewrite with list. all:cbn. all:try omega.
Qed.

Lemma sizeP_size s: sumn (map sizeT (compile s)) + 1<= 2*size s.
Proof.
  induction s;cbn.
  all:autorewrite with list. all:cbn. all:try omega.
Qed.


(** *** Programm Decomposition *)


Fixpoint jumpTarget (l:nat) (res:Pro) (P:Pro) : option (Pro*Pro) :=
  match P with
  | retT :: P => match l with
                | 0 => Some (res,P)
                | S l => jumpTarget l (res++[retT]) P
                end
  | lamT :: P => jumpTarget (S l) (res++[lamT])P
  | t :: P    => jumpTarget l (res++[t]) P
  | []        => None
  end.


Lemma jumpTarget_correct s c:
  jumpTarget 0 [] (compile s ++ retT::c) = Some (compile s,c).
Proof.
  change (Some (compile s,c)) with (jumpTarget 0 ([]++compile s) (retT::c)).
  generalize 0.
  generalize (retT::c) as c'. clear c.
  generalize (@nil Tok) as c. 
  induction s;intros c' c l.
  -reflexivity.
  -cbn. autorewrite with list. rewrite IHs1,IHs2. cbn. now autorewrite with list. 
  -cbn. autorewrite with list. rewrite IHs. cbn. now autorewrite with list.
Qed.

(** *** Program Substitution *)

Fixpoint substP (P:Pro) k Q : Pro :=
  match P with
    [] => []
  | lamT::P => lamT::substP P (S k) Q
  | retT::P => retT::match k with
                      S k => substP P k Q
                    | 0 => [(* doesnt matter *)]
                    end
  | varT k'::P => (if k' =? k then Q else [varT k'])++substP P k Q
  | appT::P => appT::substP P k Q
  end.


Lemma substP_correct' s k c' t:
  substP (compile s++c') k (compile t)
  = compile (subst s k t)++substP c' k (compile t).
Proof.
  induction s in k,c'|-*;cbn.
  -destruct (Nat.eqb_spec n k);cbn. all:now autorewrite with list.
  -autorewrite with list. rewrite IHs1,IHs2. reflexivity.
  -autorewrite with list. rewrite IHs. reflexivity. 
Qed.

Lemma substP_correct s k t:
  substP (compile s) k (compile t) = compile (subst s k t).
Proof.
  replace (compile s) with (compile s++[]) by now autorewrite with list.
  rewrite substP_correct'. now autorewrite with list. 
Qed.


(** *** Injectivity of Programm Encoding *)

Fixpoint decompile l P A : option (list term) :=
  match P with
    retT::P => match l with
                0 => None
              | S l => match A with
                        s::A => decompile l P (lam s::A)
                      | [] => None
                      end
              end
  | varT n::P => decompile l P (var n::A)
  | lamT::P =>  decompile (S l) P A
  | appT::P => match A with
               t::s::A => decompile l P (app s t::A)
             | _ => None
              end
  | [] => Some A
  end.

Lemma decompile_correct' l s P A:
  decompile l (compile s++P) A = decompile l P (s::A).
Proof.
  induction s in l,P,A|-*. all:cbn.
  -congruence.
  -autorewrite with list. rewrite IHs1. cbn. rewrite IHs2. reflexivity.
  -autorewrite with list. rewrite IHs. reflexivity.
Qed.

Lemma compile_inj s s' :
  compile s = compile s' -> s = s'.
Proof.
  intros eq.
  specialize (@decompile_correct' 0 s [] []) as H1.
  specialize (@decompile_correct' 0 s' [] []) as H2.
  rewrite eq in H1. rewrite H1 in H2. now inv H2.
Qed.
