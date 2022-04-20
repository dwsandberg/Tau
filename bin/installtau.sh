set -e
if [[ $1 == "-n" ]]; then
norun=true
fi
source bin/tauconfig.sh
checksrc wbeizer/Bcubic.html
checksrc wbeizer/Bquadratic.html
checksrc stdlib/COMPILETIME.ls
checksrc stdlib/IO2.ls
checksrc common/LEBencoding.ls
checksrc core/UTF8.ls
checksrc simple/all.decs
checksrc common/bandeskopf.ls
checksrc common/barycenter.ls
checksrc tools/baseTypeCheck.ls
checksrc stdlib/bitcast.ls
checksrc core/bits.ls
checksrc stdlib/bitstream.ls
checksrc tests/bug7.ls
checksrc tests/checking.ls
checksrc stdlib/codegennew.ls
checksrc stdlib/codetemplates.ls
checksrc stdlib/codetemplates2.ls
checksrc common/common.ls
checksrc stdlib/compileTimeT.ls
checksrc stdlib/compilerfront.ls
checksrc stdlib/compilerfrontT.ls
checksrc tools/doc.ls
checksrc tools/doc.txt
checksrc core/encoding.ls
checksrc stdlib/file.ls
checksrc stdlib/fileIO.ls
checksrc core/format.ls
checksrc tools/frontcmd.ls
checksrc webassembly/funcidx.ls
checksrc tools/genLR1.ls
checksrc core/graph.ls
checksrc stdlib/hashset.ls
checksrc stdlib/inputoutput.ls
checksrc webcore/inputoutput.ls
checksrc tools/install.txt
checksrc stdlib/internalbc.ls
checksrc webassembly/knownWfunc.ls
checksrc common/layergraph.ls
checksrc stdlib/libdesc.ls
checksrc stdlib/libraryModule.ls
checksrc stdlib/llvm.ls
checksrc stdlib/llvmconstants.ls
checksrc stdlib/localmap2.ls
checksrc stdlib/main2.ls
checksrc common/makeDAG.ls
checksrc common/matrix.ls
checksrc stdlib/mergeblocks.ls
checksrc tests/myseq.ls
checksrc stdlib/mytype.ls
checksrc common/object01.ls
checksrc core/otherseq.ls
checksrc common/packedindex.ls
checksrc stdlib/parse.ls
checksrc stdlib/parsersupport.ls
checksrc stdlib/pass2.ls
checksrc stdlib/pass2T.ls
checksrc stdlib/passparse.ls
checksrc stdlib/passsymbol.ls
checksrc stdlib/persistant.ls
checksrc common/point.ls
checksrc tests/point.ls
checksrc stdlib/postbind.ls
checksrc stdlib/pretty.ls
checksrc tools/prettycompilerfront.ls
checksrc webassembly/printfunc.ls
checksrc core/process.ls
checksrc tools/profile.ls
checksrc stdlib/ptr.ls
checksrc tests/randomphrase.ls
checksrc core/real.ls
checksrc core/seq.ls
checksrc core/set.ls
checksrc simple/simple.ls
checksrc core/sparseseq.ls
checksrc core/stack.ls
checksrc core/standard.ls
checksrc common/svg2graph.ls
checksrc stdlib/symbol.ls
checksrc stdlib/symbol2.ls
checksrc stdlib/symbolconstant.ls
checksrc stdlib/symboldict.ls
checksrc stdlib/taublockseq.ls
checksrc tools/taulextable.ls
checksrc stdlib/tausupport.ls
checksrc tests/test11.ls
checksrc tests/test11a.ls
checksrc tests/test20.ls
checksrc tests/testall.ls
checksrc tests/testencoding.ls
checksrc tests/testfileio.ls
checksrc wtests/testfileio.ls
checksrc tests/testmodules.ls
checksrc tests/testopt.ls
checksrc tests/testprocess.ls
checksrc tests/tests.ls
checksrc tests/testseq.ls
checksrc stdlib/textio.ls
checksrc stdlib/timestamp.ls
checksrc tools/tools.ls
checksrc tests/tree.ls
checksrc stdlib/typedict.ls
checksrc common/uniqueids.ls
checksrc webassembly/wasm.ls
checksrc webassembly/wasm2.ls
checksrc webassembly/wasmcompile.ls
checksrc wbeizer/wbeizer.ls
checksrc webcore/webIO.ls
checksrc webassembly/webassembly.ls
checksrc tests/wordfreq.ls
checksrc tools/wordgraph.ls
checksrc core/words.ls
checksrc wtests/wtests.html
checksrc wtests/wtests.ls
checksrc core/xxhash.ls
#________________

parts="built/compilerfront.libsrc built/orgstdlib.lib stdlib/compilerfrontT.ls stdlib/compilerfront.ls stdlib/libdesc.ls stdlib/libraryModule.ls stdlib/localmap2.ls stdlib/mytype.ls stdlib/parse.ls stdlib/parsersupport.ls stdlib/passparse.ls stdlib/passsymbol.ls stdlib/postbind.ls stdlib/symbol.ls stdlib/symboldict.ls stdlib/typedict.ls"
outofdate ||(libexe orgstdlib libsrc stdlib/compilerfrontT.ls stdlib/compilerfront.ls stdlib/libdesc.ls stdlib/libraryModule.ls stdlib/localmap2.ls stdlib/mytype.ls stdlib/parse.ls stdlib/parsersupport.ls stdlib/passparse.ls stdlib/passsymbol.ls stdlib/postbind.ls stdlib/symbol.ls stdlib/symboldict.ls stdlib/typedict.ls cmd=libsrc o=compilerfront.libsrc)

parts="built/core.libsrc built/orgstdlib.lib core/bits.ls core/encoding.ls core/format.ls core/graph.ls core/process.ls core/real.ls core/seq.ls core/set.ls core/sparseseq.ls core/stack.ls core/standard.ls core/UTF8.ls core/words.ls core/xxhash.ls core/otherseq.ls stdlib/file.ls"
outofdate ||(libexe orgstdlib libsrc core/bits.ls core/encoding.ls core/format.ls core/graph.ls core/process.ls core/real.ls core/seq.ls core/set.ls core/sparseseq.ls core/stack.ls core/standard.ls core/UTF8.ls core/words.ls core/xxhash.ls core/otherseq.ls stdlib/file.ls cmd=libsrc o=core.libsrc)
#________________

parts="built/stdlib.lib built/orgstdlib.lib built/core.libsrc built/compilerfront.libsrc stdlib/COMPILETIME.ls stdlib/bitstream.ls stdlib/codegennew.ls stdlib/codetemplates.ls stdlib/fileIO.ls stdlib/inputoutput.ls stdlib/hashset.ls stdlib/internalbc.ls stdlib/compileTimeT.ls stdlib/llvm.ls stdlib/llvmconstants.ls stdlib/main2.ls stdlib/mergeblocks.ls stdlib/pass2.ls stdlib/pass2T.ls stdlib/persistant.ls stdlib/pretty.ls stdlib/symbol2.ls stdlib/tausupport.ls stdlib/textio.ls stdlib/timestamp.ls stdlib/codetemplates2.ls stdlib/symbolconstant.ls stdlib/ptr.ls stdlib/taublockseq.ls stdlib/IO2.ls stdlib/bitcast.ls"
dependlibs=""
ccode="void init_libs(){"
outofdate ||(libexe orgstdlib libsrc built/core.libsrc built/compilerfront.libsrc stdlib/COMPILETIME.ls stdlib/bitstream.ls stdlib/codegennew.ls stdlib/codetemplates.ls stdlib/fileIO.ls stdlib/inputoutput.ls stdlib/hashset.ls stdlib/internalbc.ls stdlib/compileTimeT.ls stdlib/llvm.ls stdlib/llvmconstants.ls stdlib/main2.ls stdlib/mergeblocks.ls stdlib/pass2.ls stdlib/pass2T.ls stdlib/persistant.ls stdlib/pretty.ls stdlib/symbol2.ls stdlib/tausupport.ls stdlib/textio.ls stdlib/timestamp.ls stdlib/codetemplates2.ls stdlib/symbolconstant.ls stdlib/ptr.ls stdlib/taublockseq.ls stdlib/IO2.ls stdlib/bitcast.ls exports=UTF8 barycenter bits bitstream ptr encoding file fileIO format graph hashset internalbc ioseq layergraph libraryModule llvm llvmconstants main2 maindict makeDAG mangle otherseq pretty process real seq set sparseseq stack standard svg svggraph symbol2 taublockseq tausupport testall textio timestamp words xxhash compilerfront bitcast IO2 o=stdlib.libsrc
libexe stdlib stdlib built/stdlib.libsrc ;runlib stdlib)
#________________

parts="built/common.lib built/stdlib.lib common/common.ls common/matrix.ls common/point.ls common/packedindex.ls common/bandeskopf.ls common/uniqueids.ls common/svg2graph.ls common/makeDAG.ls common/layergraph.ls common/barycenter.ls common/object01.ls common/LEBencoding.ls"
dependlibs="built/stdlib.$libtype"
ccode="void init_stdlib(); void init_libs(){init_stdlib();"
outofdate ||(libexe stdlib libsrc common/common.ls common/matrix.ls common/point.ls common/packedindex.ls common/bandeskopf.ls common/uniqueids.ls common/svg2graph.ls common/makeDAG.ls common/layergraph.ls common/barycenter.ls common/object01.ls common/LEBencoding.ls uses=stdlib exports=matrix point packedindex bandeskopf uniqueids svg2graph makeDAG layergraph barycenter objectio object01 common o=common.libsrc
libexe stdlib stdlib built/common.libsrc ;runlib common)

parts="built/commontests.libsrc built/stdlib.lib tests/bug7.ls tests/checking.ls tests/myseq.ls tests/point.ls tests/randomphrase.ls tests/test11.ls tests/test20.ls tests/testencoding.ls tests/testmodules.ls tests/testprocess.ls tests/testseq.ls tests/tree.ls tests/wordfreq.ls"
outofdate ||(libexe stdlib libsrc tests/bug7.ls tests/checking.ls tests/myseq.ls tests/point.ls tests/randomphrase.ls tests/test11.ls tests/test20.ls tests/testencoding.ls tests/testmodules.ls tests/testprocess.ls tests/testseq.ls tests/tree.ls tests/wordfreq.ls cmd=libsrc o=commontests.libsrc)

parts="built/simple.lib built/stdlib.lib simple/simple.ls"
dependlibs="built/stdlib.$libtype"
ccode="void init_stdlib(); void init_libs(){init_stdlib();"
outofdate ||(libexe stdlib libsrc simple/simple.ls uses=stdlib exports=simple o=simple.libsrc
libexe stdlib stdlib built/simple.libsrc ;runlib simple)

parts="built/webassembly.lib built/stdlib.lib webassembly/webassembly.ls webassembly/funcidx.ls webassembly/knownWfunc.ls webassembly/printfunc.ls webassembly/wasm.ls webassembly/wasm2.ls webassembly/wasmcompile.ls"
dependlibs="built/stdlib.$libtype"
ccode="void init_stdlib(); void init_libs(){init_stdlib();"
outofdate ||(libexe stdlib libsrc webassembly/webassembly.ls webassembly/funcidx.ls webassembly/knownWfunc.ls webassembly/printfunc.ls webassembly/wasm.ls webassembly/wasm2.ls webassembly/wasmcompile.ls uses=stdlib exports=wasm wasm1 wasm2 wasmcompile webassembly o=webassembly.libsrc
libexe stdlib stdlib built/webassembly.libsrc ;runlib webassembly)
#________________

parts="built/installtau.sh built/simple.lib simple/all.decs"
outofdate ||(libexe simple updatestate simple/all.decs cmd=updatestate roots=installtau allweb o=installtau.sh)

parts="built/tests.lib built/stdlib.lib built/commontests.libsrc tests/testopt.ls tests/test11a.ls tests/testall.ls tests/tests.ls tests/testfileio.ls"
dependlibs="built/stdlib.$libtype"
ccode="void init_stdlib(); void init_libs(){init_stdlib();"
outofdate ||(libexe stdlib libsrc built/commontests.libsrc tests/testopt.ls tests/test11a.ls tests/testall.ls tests/tests.ls tests/testfileio.ls uses=stdlib exports=tests o=tests.libsrc
libexe stdlib stdlib built/tests.libsrc ;runlib tests)

parts="built/tools.lib built/stdlib.lib built/common.lib tools/tools.ls tools/baseTypeCheck.ls tools/doc.ls tools/genLR1.ls tools/prettycompilerfront.ls tools/profile.ls tools/taulextable.ls tools/frontcmd.ls tools/wordgraph.ls"
dependlibs="built/stdlib.$libtype built/common.$libtype"
ccode="void init_common(); void init_stdlib(); void init_libs(){init_stdlib(); init_common();"
outofdate ||(libexe stdlib libsrc built/common.lib tools/tools.ls tools/baseTypeCheck.ls tools/doc.ls tools/genLR1.ls tools/prettycompilerfront.ls tools/profile.ls tools/taulextable.ls tools/frontcmd.ls tools/wordgraph.ls uses=common stdlib exports=baseTypeCheck doc genLR1 profile taulextable tools uniqueids wordgraph o=tools.libsrc
libexe common common built/tools.libsrc ;runlib tools)

parts="built/webcore.libsrc built/stdlib.lib built/core.libsrc built/webassembly.lib webcore/inputoutput.ls webcore/webIO.ls common/barycenter.ls common/layergraph.ls common/makeDAG.ls common/bandeskopf.ls stdlib/tausupport.ls stdlib/textio.ls stdlib/bitstream.ls stdlib/IO2.ls stdlib/bitcast.ls stdlib/taublockseq.ls stdlib/ptr.ls"
outofdate ||(libexe stdlib libsrc built/core.libsrc built/webassembly.lib webcore/inputoutput.ls webcore/webIO.ls common/barycenter.ls common/layergraph.ls common/makeDAG.ls common/bandeskopf.ls stdlib/tausupport.ls stdlib/textio.ls stdlib/bitstream.ls stdlib/IO2.ls stdlib/bitcast.ls stdlib/taublockseq.ls stdlib/ptr.ls cmd=libsrc o=webcore.libsrc)
#________________

parts="built/baseTypeCheck.html built/tools.lib built/stdlib.libsrc"
outofdate ||(libexe tools front built/stdlib.libsrc cmd=front out=baseTypeCheck o=baseTypeCheck.html)

parts="built/callgraphwithin.html built/tools.lib built/tools.libsrc"
outofdate ||(libexe tools front built/tools.libsrc cmd=front mods=taulextable o=callgraphwithin.html)

parts="built/commondoc.html built/tools.lib built/common.libsrc"
outofdate ||(libexe tools doclibrary built/common.libsrc cmd=doclibrary o=commondoc.html)

parts="built/installdoc.html built/tools.lib tools/install.txt"
outofdate ||(libexe tools formatdoc tools/install.txt cmd=formatdoc o=installdoc.html)

parts="built/stdlibdoc.html built/tools.lib built/stdlib.libsrc"
outofdate ||(libexe tools doclibrary built/stdlib.libsrc cmd=doclibrary o=stdlibdoc.html)

parts="built/taudoc.html built/tools.lib tools/doc.txt"
outofdate ||(libexe tools formatdoc tools/doc.txt cmd=formatdoc o=taudoc.html)

parts="built/taugrammer.html built/tools.lib stdlib/parse.ls"
outofdate ||(libexe tools LR1 stdlib/parse.ls cmd=LR1 o=taugrammer.html)

parts="built/taulex.html built/tools.lib tools/install.txt"
outofdate ||(libexe tools lextable tools/install.txt cmd=lextable o=taulex.html)

parts="built/testall.html built/tests.lib"
outofdate ||(libexe tests testall cmd=testall o=testall.html)

parts="built/wbeizer.wasm built/webassembly.lib built/webcore.libsrc wbeizer/Bcubic.html wbeizer/Bquadratic.html wbeizer/wbeizer.ls"
outofdate ||(libexe webassembly wasm built/webcore.libsrc wbeizer/Bcubic.html wbeizer/Bquadratic.html wbeizer/wbeizer.ls cmd=wasm exports=wbeizer Library=wbeizer o=wbeizer.wasm)

parts="built/wtests.wasm built/webassembly.lib built/webcore.libsrc built/commontests.libsrc wtests/wtests.html wtests/wtests.ls wtests/testfileio.ls"
outofdate ||(libexe webassembly wasm built/webcore.libsrc built/commontests.libsrc wtests/wtests.html wtests/wtests.ls wtests/testfileio.ls cmd=wasm exports=wtests Library=wtests o=wtests.wasm)
#________________

parts="built/allweb.libsrc built/stdlib.lib built/wbeizer.wasm built/wtests.wasm built/testall.html built/baseTypeCheck.html built/callgraphwithin.html built/commondoc.html built/installdoc.html built/stdlibdoc.html built/taudoc.html built/taugrammer.html built/taulex.html built/testall.html"
outofdate ||(libexe stdlib libsrc built/wbeizer.wasm built/wtests.wasm built/testall.html built/baseTypeCheck.html built/callgraphwithin.html built/commondoc.html built/installdoc.html built/stdlibdoc.html built/taudoc.html built/taugrammer.html built/taulex.html built/testall.html cmd=libsrc o=allweb.libsrc)
#________________
mkbuild 