all:
	ocaml setup.ml -build
	./mosynth.native -print-modes -all -block-size 7
