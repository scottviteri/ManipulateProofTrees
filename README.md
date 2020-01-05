# ManipulateProofTrees

This package is a meant to help analyze the structural properties of proof trees exported by the Coq theorem prover. To run examples, open the org files and execute the python scripts inside.

These will automatically call the executable scripts in this package, but first you need to specify two locations on your file system.

First, in ./ProofSourceFiles/ExportProof.v, change the directory to the location of https://github.com/scottviteri/CoqAST on your local system (clone if you do not have it).
Second, change the BASE enviroment variable in ./lib_to_trees.sh to the location of your coq/theories.
If you do not have this, clone from https://github.com/coq/coq.git.

Tested with coq-8.8.

## ./ProofSourceFiles

A collection of sample Coq proofs.

## ./ProofTrees

Exported collection of reified proof trees from ./ProofSourceFiles.
Export is handled by ./coq_proof_to_trees.sh, which depends on my local version of the git repo uwplse/CoqAST.

## ./Images

The saved image outputs of computation in ManipProofTrees.org

## ./ManipProofTrees.org

Compress and analyze proof objects as a deduplified directed acyclic graph.

## ./ProofDAGs

Output of ManipProofTrees

## ./GenerateDependencyGraphs.org

Also generates a DAG from proof objects, but uses an intermediate tree representation where lemmas are substituted into main theorems. Less computationally efficient, but more conceptually clear.

Also can generate graphs of what theorems reference what other theorems in the Coq standard library.

## ./DependencyGraphs

Output of GenerateDependencyGraphs.org

## ./utils.py

Utilities used by both ManipProofTrees.org and ./GenerateDependencyGraph.org

## ./clean.sh

Wipe all saved results from ManipProofTrees.org.
