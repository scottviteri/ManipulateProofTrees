#!/bin/bash

THEOREM=$1
BASE=./ProofSourceFiles
OUTDIR=./ProofTrees/${THEOREM}
for DEPTH in 1 2 3 4 5 6;
do
 cat $BASE/ExportProofBase.v > $BASE/ExportProof.v
 cat $BASE/${THEOREM}.v >> $BASE/ExportProof.v
 echo "PrintAST ${THEOREM} with depth ${DEPTH}." >> $BASE/ExportProof.v
 mkdir -p ${OUTDIR}
 coqc $BASE/ExportProof.v > "${OUTDIR}/d${DEPTH}.txt"

 cat $BASE/ExportProofBase.v > $BASE/ExportProof.v
 cat $BASE/${THEOREM}.v >> $BASE/ExportProof.v
 echo "PrintAST ${THEOREM} with depth ${DEPTH} mod libs." >> $BASE/ExportProof.v
 coqc $BASE/ExportProof.v > "${OUTDIR}/d${DEPTH}_mod.txt"
done
