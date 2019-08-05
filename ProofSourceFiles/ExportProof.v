Add LoadPath "~/LocalSoftware/CoqAST/plugin/src/".
Add LoadPath "./ProofSourceFiles".
Require Import PrintAST.ASTPlugin.

Require Import GeoCoq.Elements.OriginalProofs.book1.
PrintAST @proposition_48 with depth 1 mod libs.
