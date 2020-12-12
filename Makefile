
all: latc
	
TestLatte: src/ParLatte.hs src/LexLatte.hs src/TestLatte.hs
	ghc -isrc --make src/TestLatte.hs -o TestLatte

latc: src/ParLatte.hs src/LexLatte.hs src/Main.hs src/TypeChecker.hs
	ghc -isrc --make src/Main.hs -o latc
	


src/LexLatte.hs: src/LexLatte.x
	alex -g $<
src/ParLatte.hs: src/ParLatte.y
	happy -gca $<

clean:
	-rm -f src/*.bak src/*.log src/*.aux src/*.hi src/*.o src/*.dvi latc latc_llvm TestLatte
	-rm -f src/LexLatte.hs src/ParLatte.hs
	-rm -f examples/*.bc examples/*.ll  examples/*.j examples/*.class

%.ll: %.lat latc_llvm
	./latc_llvm $< 




test-llvm: examples/test01.ll examples/test02.ll examples/test03.ll examples/test04.ll examples/test05.ll examples/test06.ll examples/test07.ll
	lli examples/test01.bc | cmp - examples/test01.output
	lli examples/test02.bc | cmp - examples/test02.output
	lli examples/test03.bc | cmp - examples/test03.output
	lli examples/test04.bc | cmp - examples/test04.output
	lli examples/test05.bc | cmp - examples/test05.output
	lli examples/test06.bc | cmp - examples/test06.output
	lli examples/test07.bc | cmp - examples/test07.output


dist: 
	tar -czf ks386105.tar.gz Makefile README src/  examples/
