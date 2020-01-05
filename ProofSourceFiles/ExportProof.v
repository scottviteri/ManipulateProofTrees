Add LoadPath "~/LocalSoftware/CoqAST/plugin/src/".
Add LoadPath "./ProofSourceFiles".
Require Import PrintAST.ASTPlugin.

PrintAST IVT_core with depth 9 mod libs.
