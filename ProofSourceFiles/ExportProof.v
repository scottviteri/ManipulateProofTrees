Add LoadPath "~/LocalSoftware/CoqASTSource/plugin/src/".
Add LoadPath "./ProofSourceFiles".
Require Import PrintAST.ASTPlugin.

Require Import ZArith.
PrintAST Zsqrt_le: with depth 2.
