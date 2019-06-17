# ManipulateProofTrees

./ProofSourceFiles

A collection of sample Coq proofs. Tested with coq-8.8.

./ProofTrees

Exported collection of reified proof trees from ./ProofSourceFiles.
Export is handled by ./coq_proof_to_trees.sh, which depends on my local version of the git repo uwplse/CoqAST . I have not yet made this Coq plugin available on github.

./Images

The saved image outputs of computation in ManipPfTrees.org

./Graphs

The saved graph outputs of computation in ManipPfTrees.org

./ManipPfTrees.org

The main file of this repository. Run all code and examples via emacs org mode.

./clean.sh

Wipe all saved results from ManipPfTrees.org.
Not recommended until my Coq plugin fork is uploaded.
