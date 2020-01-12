Add LoadPath "~/LocalSoftware/CoqAST/plugin/src/".
Add LoadPath "./ProofSourceFiles".
Require Import PrintAST.ASTPlugin.

Require Import CoRN.reals.RealCount.
PrintAST reals_not_countable with depth 10.
