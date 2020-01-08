Add LoadPath "~/LocalSoftware/CoqAST/plugin/src/".
Add LoadPath "./ProofSourceFiles".
Require Import PrintAST.ASTPlugin.

Add LoadPath "~/LocalSoftware/cauchy_schwarz/".
Require Import Cauchy_Schwarz.
PrintAST Cauchy_Schwarz_inequality with depth 4 mod libs.
