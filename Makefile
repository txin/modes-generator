all:
	ocaml setup.ml -build
	./mosynth.native -all -block-size 7
