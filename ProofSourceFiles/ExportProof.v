Add LoadPath "~/LocalSoftware/CoqAST/plugin/src/".
Add LoadPath "./ProofSourceFiles".
Require Import PrintAST.ASTPlugin.

Require Import ProjectiveGeometry.Plane.hexamys.
PrintAST is_hexamy with depth 6 mod libs.
