Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).

Theorem ev_2 : ev 2.
Proof. apply (ev_SS 0 ev_0). Qed.

Theorem add_even_even : forall {n m : nat}, ev m -> ev n -> ev (m + n).
Proof.
  intros n m Hm Hn.
  induction Hm.
    { simpl. apply Hn. }
    { simpl. apply ev_SS. apply IHHm. }
Qed.

Theorem ev_4_alt : ev 4.
Proof.
  apply (add_even_even ev_2 ev_2).
Qed.
