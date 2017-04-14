** This README describes the InteractiveMonitors directory contents **

Crea-date: November 2015
Authors: Zoé Drey - ENSTA Bretagne.

README History:
==============

- 01-12-2015 : (circa) preparing the interactive debugger
implementation.  This is an understood copy past of the Haskell code
of Kishon&Hudak's journal article.

- 08-12-2015 : Description of each file. 


This directory:
==============

Contains two groups of files:

- an implementation attempt of an interactive debugger.

- a parser of a "microML" language (the one for which the debugger is
written).  The goal is educational and to enable visible tests.


Summary of each file: 
=====================

- debugger : the interactive debugger implementation

- fixpoint : the okmij implementation of fixpoint (various versions,
only the native one is used)

- lexer : the LEX file to parse microML

- llambdaAlg : the semantic algebras

- llambdaAst : the abstract syntax of the language

- llambdaAstExamples : AST of a few test programs (factorial,
  fibonacci...)

- llambdaExt : internal structures for the language (part of its
  semantic algebra

- llambdaInt : the valuation functions for the interactive debugger

- debugger : the definition of the debugger as a monitor strictly
following Kishon, Hudak and Consel methodology (a monitor has its
syntax, algebras, and valuation functions - pre/pos-monitors)


To test local variable access for the debugger:
--> Annotate the program with LDebug
--> On recursive "rewind" : effective application -> effective access to required local variables.
