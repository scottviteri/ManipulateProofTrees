Add LoadPath "~/LocalSoftware/CoqAST/plugin/src/".
Add LoadPath "./ProofSourceFiles".
Require Import PrintAST.ASTPlugin.

Require Import CoRN.ftc.Taylor.
PrintAST Taylor with depth 6 mod libs.
