#!/bin/bash

PROOFS="./ProofSourceFiles"
DEPTH=$1
OUTDIR="./ProofTrees"
EUCLID_PROOFS="$HOME/.opam/4.04.0/lib/coq/user-contrib/GeoCoq/Elements/OriginalProofs"
awk 'BEGIN { FS="." } {print $(NF-1)}' "${EUCLID_PROOFS}/book1.v" > $OUTDIR/"euclid_book_d${DEPTH}.txt"
for THEOREM in $(cat ./ProofTrees/euclid_book_d${DEPTH}.txt);
do
 mkdir -p ./ProofTrees/euclid.$THEOREM

 cat ${PROOFS}/ExportProofBase.v > ${PROOFS}/ExportProof.v
 echo "Require Import GeoCoq.Elements.OriginalProofs.book1." >> ${PROOFS}/ExportProof.v
 echo "PrintAST @${THEOREM} with depth ${DEPTH}." >> ${PROOFS}/ExportProof.v
 coqc ${PROOFS}/ExportProof.v > "${OUTDIR}/euclid.${THEOREM}/d${DEPTH}.txt"

 cat ${PROOFS}/ExportProofBase.v > ${PROOFS}/ExportProof.v
 echo "Require Import GeoCoq.Elements.OriginalProofs.book1." >> ${PROOFS}/ExportProof.v
 echo "PrintAST @${THEOREM} with depth ${DEPTH} mod libs." >> ${PROOFS}/ExportProof.v
 coqc ${PROOFS}/ExportProof.v > "${OUTDIR}/euclid.${THEOREM}/d${DEPTH}_mod.txt"
done
