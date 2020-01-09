Add LoadPath "~/LocalSoftware/CoqAST/plugin/src/".
Add LoadPath "./ProofSourceFiles".
Require Import PrintAST.ASTPlugin.

Require Import mathcomp.solvable.cyclic.
PrintAST Euler_exp_totient with depth 4 mod libs.
