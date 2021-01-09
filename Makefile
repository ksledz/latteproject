
all: latc latc_llvm lib/runtime.bc
	
TestLatte: src/ParLatte.hs src/LexLatte.hs src/TestLatte.hs
	ghc -isrc --make src/TestLatte.hs -o TestLatte

latc: src/ParLatte.hs src/LexLatte.hs src/Main.hs src/TypeChecker.hs
	ghc -isrc --make src/Main.hs -o latc
	
latc_llvm: src/ParLatte.hs src/LexLatte.hs src/TypeChecker.hs src/LLVMCompiler.hs
	ghc -isrc --make src/LLVMCompiler.hs -o latc_llvm

src/LexLatte.hs: src/LexLatte.x
	alex -g $<
src/ParLatte.hs: src/ParLatte.y
	happy -gca $<

lib/runtime.bc: lib/runtime.c
	clang -c -emit-llvm lib/runtime.c -o lib/runtime.bc
clean:
	-rm -f src/*.bak src/*.log src/*.aux src/*.hi src/*.o src/*.dvi latc latc_llvm TestLatte
	-rm -f src/LexLatte.hs src/ParLatte.hs
	-rm -f examples/*.bc examples/*.ll
	-rm -f lib/runtime.bc

dist: 
	tar -czf ks386105-latte-backend.tar.gz Makefile README src/  examples/ lib/
