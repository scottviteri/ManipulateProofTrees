Add LoadPath "~/LocalSoftware/CoqAST/plugin/src/".
Add LoadPath "./ProofSourceFiles".
Require Import PrintAST.ASTPlugin.

Require Import CoRN.fta.FTA.
PrintAST FTA with depth 6 mod libs.
