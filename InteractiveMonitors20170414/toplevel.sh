#!/bin/bash

make
if [ $? -ne 0 ]
then
    echo "Compile failed."
    exit 1
fi
BUILD_DIR=$(PWD)

ocamlmktop -o ocamlMonitor str.cma \
           $BUILD_DIR/fixpoint.cmo \
           $BUILD_DIR/llambdaExt.cmo \
	         $BUILD_DIR/llambdaAst.cmo \
           $BUILD_DIR/llambdaAstExamples.cmo \
	         $BUILD_DIR/llambdaAlg.cmo \
	         $BUILD_DIR/llambdaInt.cmo \
	         $BUILD_DIR/debugger.cmo ;

rlwrap ./ocamlMonitor


