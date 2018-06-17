# Code for the ICLP 2018 paper "Certified Graph View Maintenance with Regular Datalog"

## Requirements:

Using the OPAM package manager is recommended.

 - OCaml packages: ocaml 4.06.1, fmt, cmdliner, jingoo
 - Coq Packages: Coq 8.8.0, MathComp 1.7.0
 - Generation of Experiments requires gmark [see below].

Installation using OPAM:

```
$ opam repo add coq-released http://coq.inria.fr/opam/released
$ opam update
$ opam switch 4.06.1
$ opam install coq.8.8.0 coq-mathcomp-ssreflect fmt cmdliner jingoo
```

Recall to call "eval `opam config env`" / properly configure OPAM.

## Compilation:

Type `$ make`

`./vup_main.native --help` will provide you with a list of options for running the engine.

## Experiments:

To run the `./basic_exp.native` experiment manager you need to install
a modified [gmark](https://github.com/ejgallego/gmark.git) tool from
github. The easiest way to do it is to go the `VerDILog` directory and
do:

```
$ mkdir -p external
$ git clone -b vup https://github.com/ejgallego/gmark.git external/gmark
$ make -C external/gmark/src
$ make -C external/gmark/src/querytranslate
```
