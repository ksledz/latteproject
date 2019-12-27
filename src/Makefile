all:
	happy -gca Parser/ParLatte.y
	alex -g Parser/LexLatte.x
	ghc --make Parser/TestLatte.hs -o Parser/TestLatte

clean:
	-rm -f Parser/*.log Parser/*.aux Parser/*.hi Parser/*.o Parser/*.dvi

distclean: clean
	-rm -f Parser/DocLatte.* Parser/LexLatte.* Parser/ParLatte.* Parser/LayoutLatte.* Parser/SkelLatte.* Parser/PrintLatte.* Parser/TestLatte.* Parser/AbsLatte.* Parser/TestLatte Parser/ErrM.* Parser/SharedString.* Parser/ComposOp.* Parser/Latte.dtd Parser/XMLLatte.* Makefile*
		-rmdir -p Parser/

