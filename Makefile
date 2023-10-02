.PHONY : all clean 

all:
	ghc -isrc/parser -isrc/logic -isrc/compiler -isrc/ src/Main.hs -o latc_x86 -package  mtl-2.2.2
	gcc -m32 -g -D_GNU_SOURCE -c -O lib/liblatte.c -o lib/liblatte.o

clean :
	-find . -type f \( -name '*.hi' -o -name '*.o' -o -name '*.dyn_hi' -o -name '*.dyn_o' \) -delete
	-rm -f latc_x86
