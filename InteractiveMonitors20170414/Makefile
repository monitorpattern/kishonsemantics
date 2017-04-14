# ---------------------------
# To generate documentation: make htdoc

OCAMLMAKEFILE = ./OCamlMakefile
LIBS=str unix delimcc

# ---- Source Folders -----------------
SRC_DIR = ./

# ---- Grammar Compilers --------------

CAMLYACC = menhir
# Handling camllex files
LEXSOURCES = lexer.mll 
LEXGENERATED = lexer.mli lexer.ml
# Handling camlyacc files
YACCSOURCES = parser.mly
YACCGENERATED =parser.mli parser.ml

# ---- OCamlMakefile Variables ----------


# OCAMLDOCFLAGS = 
SOURCES = $(SRC_DIR)/fixpoint.ml \
	$(SRC_DIR)/llambdaAst.ml \
	$(SRC_DIR)/llambdaAstExamples.ml \
	$(SRC_DIR)/parser.mly \
  $(SRC_DIR)/lexer.mll \
  $(SRC_DIR)/loader.ml \
	$(SRC_DIR)/llambdaExt.ml \
  $(SRC_DIR)/llambdaAlg.ml \
	$(SRC_DIR)/llambdaInt.ml \
	$(SRC_DIR)/debugger.ml \
  $(SRC_DIR)/main.ml 

DOC_FILES = $(filter %.ml, $(SOURCES))

RESULT = llambdaInt

#PACKS=unix

include $(OCAMLMAKEFILE)
