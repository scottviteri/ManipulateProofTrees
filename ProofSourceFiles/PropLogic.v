Add LoadPath "~/LocalSoftware/CoqAST/plugin/src/".
Require Import PrintAST.ASTPlugin.

Theorem t1 : forall (p q : Prop), p -> q -> p /\ q.
Proof.
  intros p q hp hq.
  split; assumption.
Qed.

PrintAST t1.

Print nat_ind.

PrintAST nat_ind.

PrintAST S.
PrintAST 0.
PrintAST (S 0).

Print conj.
PrintAST conj.
Print or.

Theorem t_assoc : forall (p q r : Prop), (p /\ q) /\ r -> p /\ (q /\ r).
Proof.
  intros p q r hpqr.
  destruct hpqr as [[hp hq] hr].
  apply (conj hp (conj hq hr)).
Qed.
Print t_assoc.
PrintAST t_assoc.

Theorem t_comm : forall (p q : Prop), p /\ q -> q /\ p.
Proof.
  intros p q hpq.
  destruct hpq as [hp hq].
  apply (conj hq hp).
Qed.

Print t_comm.

Theorem t_comms : forall (p q r : Prop), ((p /\ q) /\ r) /\ (p /\ (q /\ r)) -> p.
Proof.
  intuition.
Qed.

Print t_comms.


Theorem t2 : forall (p q r : Prop), (p /\ q) /\ (p -> r) -> r.
Proof.
  intros p q r.
  intro hpqr.
  destruct hpqr as [hpq hpr].
  destruct hpq as [hp hq].
  apply (hpr hp).
Qed.

PrintAST t2.
Print eq.

Print or.

Theorem t3 : forall (p q : Prop), not (p \/ q) -> not p.
Proof.
  intros p q hnpq hp.
  pose (hpq := or_introl hp : p \/ q).
  apply (hnpq hpq).
Qed.

Theorem t4 : forall (p q r : Prop), (p -> (q -> r)) -> (p /\ q -> r).
Proof.
  intros p q r hpqr hpq.
  destruct hpq as [hp hq].
  pose (hqr := hpqr hp : q -> r).
  apply (hqr hq).
Qed.


Theorem t5 : forall (p q : Prop), not(p \/ q) -> not p /\ not q.
Proof.
  intros p q hnpq.
  split.
  {
    intros hp.
    pose (hpq := or_introl hp : p \/ q).
    apply (hnpq hpq).
  }
  {
    intros hq.
    pose (hpq := or_intror hq : p \/ q).
    apply (hnpq hpq).
  }
Qed.

Axiom lem : forall (p : Prop), p \/ not p.

Theorem t6 : forall (p q : Prop), not (p \/ q) -> not p \/ not q.
Proof.
  intros p q hnpq.
  pose (hpnp := lem p : p \/ not p).
  destruct hpnp as [hp|hnp].
  {
    pose (hpq := or_introl hp : p \/ q).
    destruct (hnpq hpq).
  }
  {
    apply (or_introl hnp : not p \/ not q).
  }
Qed.


Theorem t7 : forall (p q : Prop), p -> (q -> p).
Proof.
  intros p q hp hq.
  apply hp.
Qed.

Theorem t8 : forall (p q : Prop), ((p /\ q) /\ not p) -> q.
Proof.
  intros p q h.
  destruct h as [hpq hnp].
  destruct hpq as [hp hq].
  apply hq.
Qed.

PrintAST t8.
