Add LoadPath "~/LocalSoftware/CoqAST/plugin/src/".
Add LoadPath "./ProofSourceFiles".
Require Import PrintAST.ASTPlugin.

Add LoadPath "/home/scottviteri/LocalSoftware/".
Require Import GeoCoq.Highschool.triangles.

Section T15.
Context `{T2D:Tarski_2D}.
Context `{TE:@Tarski_euclidean Tn TnEQD}.
PrintAST isosceles_conga with depth 6 mod libs.
