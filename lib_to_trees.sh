#!/bin/bash

PROOFS="./ProofSourceFiles"
LIB=$1
DEPTH=$2
OUTDIR="./ProofTrees/"
BASE="/home/scottviteri/LocalSoftware/coq/theories"
touch ${OUTDIR}/${LIB}_d${DEPTH}.txt
for X in ${BASE}/${LIB}/*.v;
do
 for THEOREM in $(cat $X | grep "^Theorem" | awk '{print $2}');
 do
  cat ${PROOFS}/ExportProofBase.v > ${PROOFS}/ExportProof.v
  echo "Require Import ${LIB}." >> ${PROOFS}/ExportProof.v
  echo "PrintAST ${THEOREM} with depth ${DEPTH}." >> ${PROOFS}/ExportProof.v
  mkdir -p $OUTDIR/${THEOREM}
  coqc ${PROOFS}/ExportProof.v > ${OUTDIR}/${THEOREM}/d${DEPTH}.txt
  echo ${THEOREM} >> ${OUTDIR}/${LIB}_d${DEPTH}.txt
 done
done

#Currently only matching on Theorem at beginning of line
