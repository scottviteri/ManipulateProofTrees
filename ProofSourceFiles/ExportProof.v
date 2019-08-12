Add LoadPath "~/LocalSoftware/CoqAST/plugin/src/".
Add LoadPath "./ProofSourceFiles".
Require Import PrintAST.ASTPlugin.

Require Import fourcolor.fourcolor.
PrintAST four_color with depth 6 mod libs.
