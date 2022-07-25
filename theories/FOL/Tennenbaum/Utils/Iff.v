Definition Iff A B := prod(A -> B)(B -> A).
Notation "A <=> B" := (Iff A B) (at level 70).

Fact Iff_sym A B :
  A <=> B -> B <=> A.
Proof. repeat intros []; split; auto. Qed.

Fact Iff_trans A B C :
  A <=> B -> B <=> C -> A <=> C.
Proof. repeat intros []; split; auto. Qed.