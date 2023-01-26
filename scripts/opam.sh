#!/bin/sh

OPAMDIR=$HOME/.sparkopam
OPAMROOT=$OPAMDIR/root
OPAM=$OPAMDIR/bin/opam
COMPILER=4.11.2
SWITCH=spark
OPAMFILE=opam-2.1.4-i686-linux

rm -rf $OPAMDIR
mkdir -p $OPAMDIR/bin
wget --quiet -nc https://github.com/ocaml/opam/releases/download/2.1.4/$OPAMFILE -P $OPAMDIR/bin
cp $OPAMDIR/bin/$OPAMFILE $OPAM
chmod u+x $OPAM
export PATH=$OPAMDIR/bin:$PATH
$OPAM init --quiet --bare --root=$OPAMROOT -n
export OPAMROOT
$OPAM switch create -qy $SWITCH $COMPILER
eval $(opam env --switch=$SWITCH)
$OPAM repo add coq-released https://coq.inria.fr/opam/released
opam install -qy --deps-only ./spark.opam
printf "to use opam, do the following\n"
printf "export OPAMROOT=$OPAMROOT"
printf "export PATH=\"$OPAMDIR/bin:\$PATH\"\n"
printf "eval \$(opam env --switch=$SWITCH)\n"
