Add LoadPath "~/LocalSoftware/CoqASTSource/plugin/src/".
Require Import PrintAST.ASTPlugin.

Variables P Q : nat -> Prop.

Theorem t1 : (forall (x : nat), (P x) -> (Q x)) -> (forall (x : nat), P x) -> forall (x : nat), Q x.
Proof.
  intros hxpx hxp n.
  pose (hpn := hxp n).
  pose (hpnqn := hxpx n).
  apply (hpnqn hpn).
Qed.

Print ex.


Theorem t2 : (exists (x : nat), P x) -> exists (x : nat), P x \/ Q x.
Proof.
  intros hpx.
  destruct hpx as [x hpx].

  pose (hpqx := or_introl hpx : P x \/ Q x).
