set -e
source bin/tauconfig.sh

parts="built/compilerfront.libsrc stdlib/compilerfrontT.ls stdlib/compilerfront.ls stdlib/libdesc.ls stdlib/libraryModule.ls stdlib/localmap2.ls stdlib/mytype.ls stdlib/parse.ls stdlib/parsersupport.ls stdlib/passparse.ls stdlib/passsymbol.ls stdlib/postbind.ls stdlib/symbol.ls stdlib/symboldict.ls stdlib/typedict.ls"
outofdate ||(echo "parts=$parts uses=exports=Library=compilerfront"| cat - B stdlib/compilerfrontT.ls B stdlib/compilerfront.ls B stdlib/libdesc.ls B stdlib/libraryModule.ls B stdlib/localmap2.ls B stdlib/mytype.ls B stdlib/parse.ls B stdlib/parsersupport.ls B stdlib/passparse.ls B stdlib/passsymbol.ls B stdlib/postbind.ls B stdlib/symbol.ls B stdlib/symboldict.ls B stdlib/typedict.ls > built/compilerfront.libsrc)

parts="built/core.libsrc core/bits.ls core/encoding.ls core/format.ls core/graph.ls core/process.ls core/real.ls core/seq.ls core/set.ls core/sparseseq.ls core/stack.ls core/standard.ls core/UTF8.ls core/words.ls core/xxhash.ls core/otherseq.ls stdlib/file.ls"
outofdate ||(echo "parts=$parts uses=exports=Library=core"| cat - B core/bits.ls B core/encoding.ls B core/format.ls B core/graph.ls B core/process.ls B core/real.ls B core/seq.ls B core/set.ls B core/sparseseq.ls B core/stack.ls B core/standard.ls B core/UTF8.ls B core/words.ls B core/xxhash.ls B core/otherseq.ls B stdlib/file.ls > built/core.libsrc)
#________________

parts="built/stdlib.libsrc built/core.libsrc built/compilerfront.libsrc stdlib/COMPILETIME.ls stdlib/bitstream.ls stdlib/codegennew.ls stdlib/codetemplates.ls stdlib/fileIO.ls stdlib/inputoutput.ls stdlib/hashset.ls stdlib/internalbc.ls stdlib/compileTimeT.ls stdlib/llvm.ls stdlib/llvmconstants.ls stdlib/main2.ls stdlib/mergeblocks.ls stdlib/pass2.ls stdlib/pass2T.ls stdlib/persistant.ls stdlib/pretty.ls stdlib/symbol2.ls stdlib/tausupport.ls stdlib/textio.ls stdlib/timestamp.ls stdlib/codetemplates2.ls stdlib/symbolconstant.ls stdlib/ptr.ls stdlib/taublockseq.ls stdlib/IO2.ls stdlib/bitcast.ls"
outofdate ||(echo "parts=$parts uses=exports=UTF8 barycenter bits bitstream ptr encoding file fileIO format graph hashset internalbc ioseq layergraph libraryModule llvm llvmconstants main2 maindict makeDAG mangle otherseq pretty process real seq set sparseseq stack standard svg svggraph symbol2 taublockseq tausupport testall textio timestamp words xxhash compilerfront bitcast IO2 Library=stdlib"| cat - B built/core.libsrc B built/compilerfront.libsrc B stdlib/COMPILETIME.ls B stdlib/bitstream.ls B stdlib/codegennew.ls B stdlib/codetemplates.ls B stdlib/fileIO.ls B stdlib/inputoutput.ls B stdlib/hashset.ls B stdlib/internalbc.ls B stdlib/compileTimeT.ls B stdlib/llvm.ls B stdlib/llvmconstants.ls B stdlib/main2.ls B stdlib/mergeblocks.ls B stdlib/pass2.ls B stdlib/pass2T.ls B stdlib/persistant.ls B stdlib/pretty.ls B stdlib/symbol2.ls B stdlib/tausupport.ls B stdlib/textio.ls B stdlib/timestamp.ls B stdlib/codetemplates2.ls B stdlib/symbolconstant.ls B stdlib/ptr.ls B stdlib/taublockseq.ls B stdlib/IO2.ls B stdlib/bitcast.ls > built/stdlib.libsrc)
#________________

parts="built/stdlib.lib built/stdlib.libsrc"
dependlibs=""
ccode="void init_libs(){"
outofdate ||(libexe stdlib stdlib+built stdlib.libsrc > tmp/stdlib.html ;runlib stdlib)
#________________

parts="built/common.libsrc built/stdlib.lib common/common.ls common/matrix.ls common/point.ls common/packedindex.ls common/bandeskopf.ls common/uniqueids.ls common/svg2graph.ls common/makeDAG.ls common/layergraph.ls common/barycenter.ls common/seqio.ls common/seqiohelp.ls"
outofdate ||(echo "stdlib libsrc common/common.ls common/matrix.ls common/point.ls common/packedindex.ls common/bandeskopf.ls common/uniqueids.ls common/svg2graph.ls common/makeDAG.ls common/layergraph.ls common/barycenter.ls common/seqio.ls common/seqiohelp.ls"; libexe stdlib libsrc common/common.ls common/matrix.ls common/point.ls common/packedindex.ls common/bandeskopf.ls common/uniqueids.ls common/svg2graph.ls common/makeDAG.ls common/layergraph.ls common/barycenter.ls common/seqio.ls common/seqiohelp.ls cmd=libsrc uses=stdlib exports=matrix point seqio seqiohelp packedindex bandeskopf uniqueids svg2graph makeDAG layergraph barycenter Library=common o=common.libsrc > /dev/null)

parts="built/commontests.libsrc built/stdlib.lib tests/bug7.ls tests/checking.ls tests/myseq.ls tests/point.ls tests/randomphrase.ls tests/test11.ls tests/test20.ls tests/testencoding.ls tests/testmodules.ls tests/testprocess.ls tests/testseq.ls tests/tree.ls tests/wordfreq.ls"
outofdate ||(echo "stdlib libsrc tests/bug7.ls tests/checking.ls tests/myseq.ls tests/point.ls tests/randomphrase.ls tests/test11.ls tests/test20.ls tests/testencoding.ls tests/testmodules.ls tests/testprocess.ls tests/testseq.ls tests/tree.ls tests/wordfreq.ls"; libexe stdlib libsrc tests/bug7.ls tests/checking.ls tests/myseq.ls tests/point.ls tests/randomphrase.ls tests/test11.ls tests/test20.ls tests/testencoding.ls tests/testmodules.ls tests/testprocess.ls tests/testseq.ls tests/tree.ls tests/wordfreq.ls cmd=libsrc Library=commontests o=commontests.libsrc > /dev/null)

parts="built/simple.libsrc built/stdlib.lib simple/simple.ls"
outofdate ||(echo "stdlib libsrc simple/simple.ls"; libexe stdlib libsrc simple/simple.ls cmd=libsrc uses=stdlib exports=simple Library=simple o=simple.libsrc > /dev/null)
#________________

parts="built/common.lib built/common.libsrc"
dependlibs="built/stdlib.$libtype"
ccode="void init_stdlib(); void init_libs(){init_stdlib();"
outofdate ||(libexe stdlib stdlib+built common.libsrc > tmp/common.html ;runlib common)

parts="built/simple.lib built/simple.libsrc"
dependlibs="built/stdlib.$libtype"
ccode="void init_stdlib(); void init_libs(){init_stdlib();"
outofdate ||(libexe stdlib stdlib+built simple.libsrc > tmp/simple.html ;runlib simple)

parts="built/tests.libsrc built/stdlib.lib built/commontests.libsrc tests/testopt.ls tests/test11a.ls tests/testall.ls tests/tests.ls tests/testfileio.ls"
outofdate ||(echo "stdlib libsrc built/commontests.libsrc tests/testopt.ls tests/test11a.ls tests/testall.ls tests/tests.ls tests/testfileio.ls"; libexe stdlib libsrc built/commontests.libsrc tests/testopt.ls tests/test11a.ls tests/testall.ls tests/tests.ls tests/testfileio.ls cmd=libsrc uses=stdlib exports=tests Library=tests o=tests.libsrc > /dev/null)
#________________

parts="built/installtau.sh built/simple.lib simple/all.decs"
outofdate ||(echo "simple updatestate simple/all.decs"; libexe simple updatestate simple/all.decs cmd=updatestate roots=installtau allweb o=installtau.sh > /dev/null)

parts="built/tests.lib built/tests.libsrc"
dependlibs="built/stdlib.$libtype"
ccode="void init_stdlib(); void init_libs(){init_stdlib();"
outofdate ||(libexe stdlib stdlib+built tests.libsrc > tmp/tests.html ;runlib tests)

parts="built/tools.libsrc built/common.lib tools/tools.ls tools/baseTypeCheck.ls tools/doc.ls tools/genLR1.ls tools/prettycompilerfront.ls tools/profile.ls tools/taulextable.ls tools/frontcmd.ls tools/wordgraph.ls"
outofdate ||(echo "parts=$parts uses=common stdlib exports=baseTypeCheck doc genLR1 profile taulextable tools uniqueids wordgraph Library=tools"| cat - B tools/tools.ls B tools/baseTypeCheck.ls B tools/doc.ls B tools/genLR1.ls B tools/prettycompilerfront.ls B tools/profile.ls B tools/taulextable.ls B tools/frontcmd.ls B tools/wordgraph.ls > built/tools.libsrc)
#________________

parts="built/testall.html built/tests.lib"
outofdate ||(echo "tests testall"; libexe tests testall cmd=testall o=testall.html > /dev/null)

parts="built/tools.lib built/tools.libsrc"
dependlibs="built/stdlib.$libtype built/common.$libtype"
ccode="void init_common(); void init_stdlib(); void init_libs(){init_stdlib(); init_common();"
outofdate ||(libexe common common+built tools.libsrc > tmp/tools.html ;runlib tools)
#________________

parts="built/baseTypeCheck.html built/tools.lib built/stdlib.libsrc"
outofdate ||(echo "tools front built/stdlib.libsrc"; libexe tools front built/stdlib.libsrc cmd=front out=baseTypeCheck o=baseTypeCheck.html > /dev/null)

parts="built/callgraphwithin.html built/tools.lib built/tools.libsrc"
outofdate ||(echo "tools front built/tools.libsrc"; libexe tools front built/tools.libsrc cmd=front mods=taulextable o=callgraphwithin.html > /dev/null)

parts="built/commondoc.html built/tools.lib built/common.libsrc"
outofdate ||(echo "tools doclibrary built/common.libsrc"; libexe tools doclibrary built/common.libsrc cmd=doclibrary o=commondoc.html > /dev/null)

parts="built/installdoc.html built/tools.lib tools/install.txt"
outofdate ||(echo "tools formatdoc tools/install.txt"; libexe tools formatdoc tools/install.txt cmd=formatdoc o=installdoc.html > /dev/null)

parts="built/stdlibdoc.html built/tools.lib built/stdlib.libsrc"
outofdate ||(echo "tools doclibrary built/stdlib.libsrc"; libexe tools doclibrary built/stdlib.libsrc cmd=doclibrary o=stdlibdoc.html > /dev/null)

parts="built/taudoc.html built/tools.lib tools/doc.txt"
outofdate ||(echo "tools formatdoc tools/doc.txt"; libexe tools formatdoc tools/doc.txt cmd=formatdoc o=taudoc.html > /dev/null)

parts="built/taugrammer.html built/tools.lib stdlib/parse.ls"
outofdate ||(echo "tools LR1 stdlib/parse.ls"; libexe tools LR1 stdlib/parse.ls cmd=LR1 o=taugrammer.html > /dev/null)

parts="built/taulex.html built/tools.lib tools/install.txt"
outofdate ||(echo "tools lextable tools/install.txt"; libexe tools lextable tools/install.txt cmd=lextable o=taulex.html > /dev/null)
#________________

parts="built/allweb.libsrc built/wbeizer.html built/wtests.html built/testall.html built/baseTypeCheck.html built/callgraphwithin.html built/commondoc.html built/installdoc.html built/stdlibdoc.html built/taudoc.html built/taugrammer.html built/taulex.html built/tests.html"
outofdate ||(echo "parts=$parts uses=exports=Library=allweb"| cat - > built/allweb.libsrc)
#________________ 