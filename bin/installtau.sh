set -e
source bin/tauconfig.sh

parts="built/compilerfront.libsrc stdlib/compilerfrontT.ls stdlib/compilerfront.ls stdlib/libdesc.ls stdlib/libraryModule.ls stdlib/localmap2.ls stdlib/mytype.ls stdlib/parse.ls stdlib/parsersupport.ls stdlib/passparse.ls stdlib/passsymbol.ls stdlib/postbind.ls stdlib/symbol.ls stdlib/symboldict.ls stdlib/typedict.ls"
outofdate ||(echo "parts=$parts uses=exports=Library=compilerfront"| cat - B stdlib/compilerfrontT.ls B stdlib/compilerfront.ls B stdlib/libdesc.ls B stdlib/libraryModule.ls B stdlib/localmap2.ls B stdlib/mytype.ls B stdlib/parse.ls B stdlib/parsersupport.ls B stdlib/passparse.ls B stdlib/passsymbol.ls B stdlib/postbind.ls B stdlib/symbol.ls B stdlib/symboldict.ls B stdlib/typedict.ls > built/compilerfront.libsrc)

parts="built/core.libsrc core/bits.ls core/encoding.ls core/format.ls core/graph.ls core/process.ls core/real.ls core/seq.ls core/set.ls core/sparseseq.ls core/stack.ls core/standard.ls core/UTF8.ls core/words.ls core/xxhash.ls core/otherseq.ls stdlib/file.ls"
outofdate ||(echo "parts=$parts uses=exports=Library=core"| cat - B core/bits.ls B core/encoding.ls B core/format.ls B core/graph.ls B core/process.ls B core/real.ls B core/seq.ls B core/set.ls B core/sparseseq.ls B core/stack.ls B core/standard.ls B core/UTF8.ls B core/words.ls B core/xxhash.ls B core/otherseq.ls B stdlib/file.ls > built/core.libsrc)

parts="built/opttests.libsrc tests/opttests.ls"
outofdate ||(echo "parts=$parts uses=stdlib exports=opttests Library=opttests"| cat - B tests/opttests.ls > built/opttests.libsrc)
#________________

parts="built/stdlib.libsrc built/core.libsrc built/compilerfront.libsrc stdlib/COMPILETIME.ls stdlib/bitstream.ls stdlib/codegennew.ls stdlib/codetemplates.ls stdlib/fileIO.ls stdlib/inputoutput.ls stdlib/hashset.ls stdlib/internalbc.ls stdlib/compileTimeT.ls stdlib/llvm.ls stdlib/llvmconstants.ls stdlib/main2.ls stdlib/mergeblocks.ls stdlib/pass2.ls stdlib/pass2T.ls stdlib/persistant.ls stdlib/pretty.ls stdlib/symbol2.ls stdlib/tausupport.ls stdlib/textio.ls stdlib/timestamp.ls stdlib/codetemplates2.ls stdlib/symbolconstant.ls stdlib/ptr.ls stdlib/taublockseq.ls stdlib/IO2.ls stdlib/bitcast.ls"
outofdate ||(echo "parts=$parts uses=exports=UTF8 barycenter bits bitstream ptr encoding file fileIO format graph hashset internalbc ioseq layergraph libraryModule llvm llvmconstants main2 maindict makeDAG mangle otherseq pretty process real seq set sparseseq stack standard svg svggraph symbol2 taublockseq tausupport testall textio timestamp words xxhash compilerfront bitcast IO2 Library=stdlib"| cat - B built/core.libsrc B built/compilerfront.libsrc B stdlib/COMPILETIME.ls B stdlib/bitstream.ls B stdlib/codegennew.ls B stdlib/codetemplates.ls B stdlib/fileIO.ls B stdlib/inputoutput.ls B stdlib/hashset.ls B stdlib/internalbc.ls B stdlib/compileTimeT.ls B stdlib/llvm.ls B stdlib/llvmconstants.ls B stdlib/main2.ls B stdlib/mergeblocks.ls B stdlib/pass2.ls B stdlib/pass2T.ls B stdlib/persistant.ls B stdlib/pretty.ls B stdlib/symbol2.ls B stdlib/tausupport.ls B stdlib/textio.ls B stdlib/timestamp.ls B stdlib/codetemplates2.ls B stdlib/symbolconstant.ls B stdlib/ptr.ls B stdlib/taublockseq.ls B stdlib/IO2.ls B stdlib/bitcast.ls > built/stdlib.libsrc)
#________________

parts="built/stdlib.lib built/stdlib.libsrc"
dependlibs=""
ccode="void init_libs(){"
outofdate ||(libexe stdlib stdlib > tmp/stdlib.html ;runlib stdlib)
#________________

parts="built/common.libsrc built/stdlib.lib common/common.ls common/matrix.ls common/point.ls common/seqio.ls common/seqiohelp.ls common/packedindex.ls common/bandeskopf.ls common/uniqueids.ls common/svg2graph.ls common/makeDAG.ls common/layergraph.ls common/barycenter.ls"
outofdate ||(echo "parts=$parts uses=stdlib exports=common matrix point seqio seqiohelp packedindex bandeskopf uniqueids svg2graph makeDAG layergraph barycenter Library=common"| cat - B common/common.ls B common/matrix.ls B common/point.ls B common/seqio.ls B common/seqiohelp.ls B common/packedindex.ls B common/bandeskopf.ls B common/uniqueids.ls B common/svg2graph.ls B common/makeDAG.ls B common/layergraph.ls B common/barycenter.ls > built/common.libsrc)

parts="built/simple.libsrc built/stdlib.lib simple/simple.ls"
outofdate ||(echo "parts=$parts uses=stdlib exports=simple Library=simple"| cat - B simple/simple.ls > built/simple.libsrc)

parts="built/tests.libsrc built/stdlib.lib built/opttests.libsrc tests/tests.ls tests/bug7.ls tests/checking.ls tests/myseq.ls tests/point.ls tests/randomphrase.ls tests/test11.ls tests/test20.ls tests/testencoding.ls tests/testfileio.ls tests/testmodules.ls tests/testprocess.ls tests/test11a.ls tests/testall.ls tests/testopt.ls tests/testseq.ls tests/wordfreq.ls tests/tree.ls"
outofdate ||(echo "parts=$parts uses=stdlib exports=tests Library=tests"| cat - B built/opttests.libsrc B tests/tests.ls B tests/bug7.ls B tests/checking.ls B tests/myseq.ls B tests/point.ls B tests/randomphrase.ls B tests/test11.ls B tests/test20.ls B tests/testencoding.ls B tests/testfileio.ls B tests/testmodules.ls B tests/testprocess.ls B tests/test11a.ls B tests/testall.ls B tests/testopt.ls B tests/testseq.ls B tests/wordfreq.ls B tests/tree.ls > built/tests.libsrc)

parts="built/webassembly.libsrc built/stdlib.lib webassembly/webassembly.ls webassembly/funcidx.ls webassembly/knownWfunc.ls webassembly/printfunc.ls webassembly/wasm.ls webassembly/wasm2.ls webassembly/wasmcompile.ls"
outofdate ||(echo "parts=$parts uses=stdlib exports=wasm wasm1 wasm2 wasmcompile webassembly Library=webassembly"| cat - B webassembly/webassembly.ls B webassembly/funcidx.ls B webassembly/knownWfunc.ls B webassembly/printfunc.ls B webassembly/wasm.ls B webassembly/wasm2.ls B webassembly/wasmcompile.ls > built/webassembly.libsrc)
#________________

parts="built/common.lib built/common.libsrc"
dependlibs="built/stdlib.$libtype"
ccode="void init_stdlib(); void init_libs(){init_stdlib();"
outofdate ||(libexe stdlib common > tmp/common.html ;runlib common)

parts="built/simple.lib built/simple.libsrc"
dependlibs="built/stdlib.$libtype"
ccode="void init_stdlib(); void init_libs(){init_stdlib();"
outofdate ||(libexe stdlib simple > tmp/simple.html ;runlib simple)

parts="built/tests.lib built/tests.libsrc"
dependlibs="built/stdlib.$libtype"
ccode="void init_stdlib(); void init_libs(){init_stdlib();"
outofdate ||(libexe stdlib tests > tmp/tests.html ;runlib tests)

parts="built/webassembly.lib built/webassembly.libsrc"
dependlibs="built/stdlib.$libtype"
ccode="void init_stdlib(); void init_libs(){init_stdlib();"
outofdate ||(libexe stdlib webassembly > tmp/webassembly.html ;runlib webassembly)
#________________

parts="built/installtau.tau built/simple.lib simple/all.decs"
outofdate ||(echo "simple updatestate simple/all.decs"; libexe simple updatestate simple/all.decs cmd=updatestate roots=installtau allweb > built/installtau.html ; ln -f built/installtau.html built/installtau.tau)

parts="built/testall.tau built/tests.lib"
outofdate ||(echo "tests testall"; libexe tests testall cmd=testall > built/testall.html ; ln -f built/testall.html built/testall.tau)

parts="built/tools.libsrc built/common.lib tools/tools.ls tools/baseTypeCheck.ls tools/doc.ls tools/genLR1.ls tools/prettycompilerfront.ls tools/profile.ls tools/taulextable.ls tools/frontcmd.ls tools/wordgraph.ls"
outofdate ||(echo "parts=$parts uses=common stdlib exports=baseTypeCheck doc genLR1 profile taulextable tools uniqueids wordgraph Library=tools"| cat - B tools/tools.ls B tools/baseTypeCheck.ls B tools/doc.ls B tools/genLR1.ls B tools/prettycompilerfront.ls B tools/profile.ls B tools/taulextable.ls B tools/frontcmd.ls B tools/wordgraph.ls > built/tools.libsrc)

parts="built/webcore.libsrc built/core.libsrc built/webassembly.lib webcore/inputoutput.ls webcore/webIO.ls common/barycenter.ls common/layergraph.ls common/makeDAG.ls common/bandeskopf.ls stdlib/tausupport.ls stdlib/textio.ls stdlib/bitstream.ls stdlib/IO2.ls stdlib/bitcast.ls stdlib/taublockseq.ls stdlib/ptr.ls"
outofdate ||(echo "parts=$parts uses=exports=Library=webcore"| cat - B built/core.libsrc B webcore/inputoutput.ls B webcore/webIO.ls B common/barycenter.ls B common/layergraph.ls B common/makeDAG.ls B common/bandeskopf.ls B stdlib/tausupport.ls B stdlib/textio.ls B stdlib/bitstream.ls B stdlib/IO2.ls B stdlib/bitcast.ls B stdlib/taublockseq.ls B stdlib/ptr.ls > built/webcore.libsrc)
#________________

parts="built/tools.lib built/tools.libsrc"
dependlibs="built/stdlib.$libtype built/common.$libtype"
ccode="void init_common(); void init_stdlib(); void init_libs(){init_stdlib(); init_common();"
outofdate ||(libexe common tools > tmp/tools.html ;runlib tools)

parts="built/wbeizer.libsrc built/webcore.libsrc wbeizer/wbeizer.ls wbeizer/Bquadratic.html wbeizer/Bcubic.html"
outofdate ||(echo "parts=$parts uses=exports=wbeizer Library=wbeizer"| cat - B built/webcore.libsrc B wbeizer/wbeizer.ls > built/wbeizer.libsrc)

parts="built/wtests.libsrc built/webcore.libsrc wtests/wtests.ls wtests/testfileio.ls wtests/wtests.html tests/tree.ls tests/wordfreq.ls tests/checking.ls tests/test11.ls tests/point.ls tests/testencoding.ls tests/testmodules.ls tests/testprocess.ls tests/randomphrase.ls tests/test20.ls tests/myseq.ls tests/testseq.ls tests/bug7.ls"
outofdate ||(echo "parts=$parts uses=exports=wtests Library=wtests"| cat - B built/webcore.libsrc B wtests/wtests.ls B wtests/testfileio.ls B tests/tree.ls B tests/wordfreq.ls B tests/checking.ls B tests/test11.ls B tests/point.ls B tests/testencoding.ls B tests/testmodules.ls B tests/testprocess.ls B tests/randomphrase.ls B tests/test20.ls B tests/myseq.ls B tests/testseq.ls B tests/bug7.ls > built/wtests.libsrc)
#________________

parts="built/baseTypeCheck.tau built/tools.lib built/stdlib.libsrc"
outofdate ||(echo "tools front built/stdlib.libsrc"; libexe tools front built/stdlib.libsrc cmd=front out=baseTypeCheck > built/baseTypeCheck.html ; ln -f built/baseTypeCheck.html built/baseTypeCheck.tau)

parts="built/callgraphwithin.tau built/tools.lib built/tools.libsrc"
outofdate ||(echo "tools front built/tools.libsrc"; libexe tools front built/tools.libsrc cmd=front mods=taulextable > built/callgraphwithin.html ; ln -f built/callgraphwithin.html built/callgraphwithin.tau)

parts="built/commondoc.tau built/tools.lib built/common.libsrc"
outofdate ||(echo "tools doclibrary built/common.libsrc"; libexe tools doclibrary built/common.libsrc cmd=doclibrary > built/commondoc.html ; ln -f built/commondoc.html built/commondoc.tau)

parts="built/installdoc.tau built/tools.lib tools/install.txt"
outofdate ||(echo "tools formatdoc tools/install.txt"; libexe tools formatdoc tools/install.txt cmd=formatdoc > built/installdoc.html ; ln -f built/installdoc.html built/installdoc.tau)

parts="built/stdlibdoc.tau built/tools.lib built/stdlib.libsrc"
outofdate ||(echo "tools doclibrary built/stdlib.libsrc"; libexe tools doclibrary built/stdlib.libsrc cmd=doclibrary > built/stdlibdoc.html ; ln -f built/stdlibdoc.html built/stdlibdoc.tau)

parts="built/taudoc.tau built/tools.lib tools/doc.txt"
outofdate ||(echo "tools formatdoc tools/doc.txt"; libexe tools formatdoc tools/doc.txt cmd=formatdoc > built/taudoc.html ; ln -f built/taudoc.html built/taudoc.tau)

parts="built/taugrammer.tau built/tools.lib stdlib/parse.ls"
outofdate ||(echo "tools LR1 stdlib/parse.ls"; libexe tools LR1 stdlib/parse.ls cmd=LR1 > built/taugrammer.html ; ln -f built/taugrammer.html built/taugrammer.tau)

parts="built/taulex.tau built/tools.lib tools/install.txt"
outofdate ||(echo "tools lextable tools/install.txt"; libexe tools lextable tools/install.txt cmd=lextable > built/taulex.html ; ln -f built/taulex.html built/taulex.tau)

parts="built/wbeizer.wexe built/wbeizer.libsrc"
outofdate || runwexe wbeizer

parts="built/wtests.wexe built/wtests.libsrc"
outofdate || runwexe wtests
#________________

parts="built/allweb.libsrc built/wbeizer.wexe built/wtests.wexe built/testall.tau built/baseTypeCheck.tau built/callgraphwithin.tau built/commondoc.tau built/installdoc.tau built/stdlibdoc.tau built/taudoc.tau built/taugrammer.tau built/taulex.tau built/tests.s"
outofdate ||(echo "parts=$parts uses=exports=Library=allweb"| cat - > built/allweb.libsrc)
#________________ 