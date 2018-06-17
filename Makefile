.PHONY: all clean

VFILES:=$(shell ls *.v)
#MLFILES:=$(shell ls vup_base/*.ml)

all: Makefile.coq vfile-stamp #mlfile-stamp

Makefile.coq: _CoqProject
	coq_makefile -arg '-w -notation-overridden' -f _CoqProject -o Makefile.coq

html: Makefile.coq
	make -f Makefile.coq html

vup_coq:
	mkdir -p vup_coq

vfile-stamp: $(VFILES) vup_coq
	make -f Makefile.coq
	touch vfile-stamp

mlfile-stamp: vfile-stamp $(MLFILES)
	ocamlbuild -use-ocamlfind vup_base/vup_main.native
	ocamlbuild -use-ocamlfind vup_base/basic_exp.native

clean: Makefile.coq
	ocamlbuild -clean
	make -f Makefile.coq clean
	rm -rf Makefile.coq Makefile.coq.conf mlfile-stamp vfile-stamp vup_coq
