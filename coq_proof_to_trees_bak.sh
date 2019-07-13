#!/bin/bash

THEOREM=$1
BASE=./ProofSourceFiles
OUTDIR=./ProofTrees/${THEOREM}
for DEPTH in 1 2 3 4 5 6 7 8 9;
do
 coqc ${BASE}/${THEOREM}.v
 cat $BASE/ExportProofBase.v > $BASE/ExportProof.v
 echo "Require Import ${THEOREM}." >> $BASE/ExportProof.v
 echo "PrintAST ${THEOREM} with depth ${DEPTH}." >> $BASE/ExportProof.v
 mkdir -p ${OUTDIR}
 coqc $BASE/ExportProof.v > "${OUTDIR}/d${DEPTH}.txt"
done
