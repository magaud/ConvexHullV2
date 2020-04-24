COQTOP=coqtop
COQDOC=coqdoc
COQDEP=coqdep
COQC=coqc

# OCAMLC=ocamlc
# OCAMLDEP=ocamldep

all:	Del13.vo CH07_CH.vo # 5_m1m6.vo CH06_CHID.vo

%.vo:	%.v
	$(COQC) $*

%.cmo:	%.ml
	$(OCAMLC) -c $< 

%.cmi:	%.mli
	$(OCAMLC) -c $< 

web:	*.vo
	$(COQDOC) --no-externals -l -g --glob-from glob.data *.v

ch:	main.cmo fmaps.cmo
	$(OCAMLC) -o ch graphics.cma fmaps.cmo main.cmo

clean:	
	rm -rf *.g *.vo *.html *~ glob.data *.glob *.cmo *.cmi ch fmaps.*

depend:	
#	ocamldep *.ml > make
	$(COQDEP) -I . *.v >> Make

include Make
