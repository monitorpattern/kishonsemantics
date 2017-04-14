# ---------------------------
# To generate documentation: make htdoc

OCAMLMAKEFILE = ./OCamlMakefile
LIBS=str unix delimcc

# ---- Source Folders -----------------
SRC_DIR = ./

# ---- OCamlMakefile Variables ----------

# OCAMLDOCFLAGS = 
SOURCES = $(SRC_DIR)/fixpoint.ml \
	$(SRC_DIR)/llambdaAnn.ml \
	$(SRC_DIR)/llambdaTests.ml \
	$(SRC_DIR)/profiler.ml \
	$(SRC_DIR)/profiler2.ml \
	$(SRC_DIR)/tracer.ml \
	$(SRC_DIR)/demon.ml	\
	$(SRC_DIR)/demon2.ml \
	$(SRC_DIR)/collectingMonitor.ml

#	$(SRC_DIR)/annotator.ml 
#	$(SRC_DIR)/tracer.ml	


DOC_FILES = $(filter %.ml, $(SOURCES))

RESULT = llambdaAnn

#PACKS=unix

include $(OCAMLMAKEFILE)
