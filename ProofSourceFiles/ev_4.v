Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).

Theorem ev_2 : ev 2.
Proof. apply (ev_SS 0 ev_0). Qed.

Theorem ev_4 : ev 4.
Proof. apply (ev_SS 2 ev_2). Qed.

Theorem ev_8 : ev 8.
Proof. apply (ev_SS 6 (ev_SS 4 ev_4)). Qed.



