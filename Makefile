all:
	ocaml setup.ml -build
	./mosynth.native -src 2 -xor 1 -prf 2
