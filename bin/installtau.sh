set -e
if [[ $1 == "-n" ]]; then
norun=true
fi
source bin/tauconfig.sh
checksrc wbeizer/Bcubic.html
checksrc wbeizer/Bquadratic.html
checksrc stdlib/COMPILETIME.ls
checksrc stdlib/LEBencoding.ls
checksrc core/UTF8.ls
checksrc bin/all.decs
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
checksrc stdlib/debuginfo.ls
checksrc tools/doc.ls
checksrc tools/doc.txt
checksrc core/encoding.ls
checksrc stdlib/file.ls
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
checksrc stdlib/llvm.ls
checksrc stdlib/llvmconstants.ls
checksrc stdlib/localmap2.ls
checksrc stdlib/main2.ls
checksrc webtools/main2.ls
checksrc common/makeDAG.ls
checksrc common/matrix.ls
checksrc stdlib/mergeblocks.ls
checksrc tests/myseq.ls
checksrc stdlib/mytype.ls
checksrc stdlib/object01.ls
checksrc stdlib/objectio.ls
checksrc tests/opttests.ls
checksrc core/otherseq.ls
checksrc stdlib/parse.ls
checksrc stdlib/parsersupport.ls
checksrc stdlib/pass2.ls
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
checksrc tests/testmodules.ls
checksrc tests/testopt.ls
checksrc tests/testprocess.ls
checksrc tests/testseq.ls
checksrc stdlib/textio.ls
checksrc stdlib/timestamp.ls
checksrc tools/tools.ls
checksrc tests/tree.ls
checksrc stdlib/typedict.ls
checksrc common/uniqueids.ls
checksrc stdlib/updatestate.ls
checksrc webassembly/wasm.ls
checksrc webassembly/wasm2.ls
checksrc webassembly/wasmcompile.ls
checksrc wbeizer/wbeizer.ls
checksrc webcore/webIO.ls
checksrc webassembly/webassembly.ls
checksrc webtools/webtools.html
checksrc webtools/webtools.ls
checksrc tests/wordfreq.ls
checksrc tools/wordgraph.ls
checksrc core/words.ls
checksrc core/xxhash.ls
#________________

parts3="stdlib/pretty.ls stdlib/symbol2.ls stdlib/symbolconstant.ls stdlib/compilerfrontT.ls stdlib/compilerfront.ls stdlib/mergeblocks.ls stdlib/pass2.ls stdlib/localmap2.ls stdlib/mytype.ls stdlib/parse.ls stdlib/parsersupport.ls stdlib/passparse.ls stdlib/passsymbol.ls stdlib/postbind.ls stdlib/symbol.ls stdlib/symboldict.ls stdlib/typedict.ls"
node="built/compilerfront.libsrc"
part1="built/orgstdlib.lib"
(libexeAll orgstdlib libsrc $parts3 o=compilerfront.libsrc)

parts3="core/bits.ls core/encoding.ls core/format.ls core/graph.ls core/process.ls core/real.ls core/seq.ls core/set.ls core/sparseseq.ls core/stack.ls core/standard.ls core/UTF8.ls core/words.ls core/xxhash.ls core/otherseq.ls stdlib/textio.ls"
node="built/core.libsrc"
part1="built/orgstdlib.lib"
(libexeAll orgstdlib libsrc $parts3 o=core.libsrc)
#________________

parts3="built/core.libsrc built/compilerfront.libsrc stdlib/updatestate.ls stdlib/debuginfo.ls stdlib/COMPILETIME.ls stdlib/bitstream.ls stdlib/codegennew.ls stdlib/codetemplates.ls stdlib/file.ls stdlib/inputoutput.ls stdlib/hashset.ls stdlib/internalbc.ls stdlib/llvm.ls stdlib/llvmconstants.ls stdlib/main2.ls stdlib/persistant.ls stdlib/symbol2.ls stdlib/tausupport.ls stdlib/compileTimeT.ls stdlib/timestamp.ls stdlib/codetemplates2.ls stdlib/ptr.ls stdlib/taublockseq.ls stdlib/bitcast.ls stdlib/object01.ls stdlib/objectio.ls stdlib/LEBencoding.ls"
part1="built/orgstdlib.lib"
libsrcargs="orgstdlib libsrc $parts3 exports=midpoint inputoutput mytype UTF8 barycenter bits bitstream ptr encoding file format graph hashset internalbc ioseq layergraph debuginfo llvm llvmconstants main2 maindict makeDAG mangle otherseq pretty process real seq set sparseseq stack standard svg svggraph symbol2 taublockseq tausupport testall textio timestamp words xxhash compilerfront bitcast objectio object01 LEBencoding o=stdlib.libsrc"
compileargs="stdlib stdlib built/stdlib.libsrc"
dependlibs=""
ccode="void init_libs(){"
makelibrary stdlib
#________________

parts3="common/common.ls common/matrix.ls common/point.ls common/bandeskopf.ls common/uniqueids.ls common/svg2graph.ls common/makeDAG.ls common/layergraph.ls common/barycenter.ls"
part1="built/stdlib.lib"
libsrcargs="stdlib libsrc $parts3 uses=stdlib exports=matrix point bandeskopf uniqueids svg2graph makeDAG layergraph barycenter common o=common.libsrc"
compileargs="stdlib stdlib built/common.libsrc built/stdlib.libinfo"
dependlibs="built/stdlib.$libtype"
ccode="void init_stdlib(); void init_libs(){init_stdlib();"
makelibrary common

parts3="bin/all.decs"
node="built/installtau.sh"
part1="built/stdlib.lib"
(libexeAll stdlib updatestate $parts3 o=installtau.sh)

parts3="tests/bug7.ls tests/checking.ls tests/myseq.ls tests/point.ls tests/randomphrase.ls tests/test11.ls tests/test20.ls tests/testencoding.ls tests/testmodules.ls tests/testprocess.ls tests/testseq.ls tests/tree.ls tests/wordfreq.ls tests/testopt.ls tests/test11a.ls tests/testall.ls"
part1="built/stdlib.lib"
libsrcargs="stdlib libsrc $parts3 uses=stdlib exports=tests o=tests.libsrc"
compileargs="stdlib stdlib built/tests.libsrc built/stdlib.libinfo"
dependlibs="built/stdlib.$libtype"
ccode="void init_stdlib(); void init_libs(){init_stdlib();"
makelibrary tests

parts3="webassembly/webassembly.ls webassembly/funcidx.ls webassembly/knownWfunc.ls webassembly/printfunc.ls webassembly/wasm.ls webassembly/wasm2.ls webassembly/wasmcompile.ls"
part1="built/stdlib.lib"
libsrcargs="stdlib libsrc $parts3 uses=stdlib exports=wasm wasm1 wasm2 wasmcompile webassembly o=webassembly.libsrc"
compileargs="stdlib stdlib built/webassembly.libsrc built/stdlib.libinfo"
dependlibs="built/stdlib.$libtype"
ccode="void init_stdlib(); void init_libs(){init_stdlib();"
makelibrary webassembly
#________________

parts3="tests/opttests.ls built/stdlib.libinfo"
node="built/testall.html"
part1="built/tests.lib"
(libexeAll tests testall $parts3 o=testall.html)

parts3="built/common.lib tools/tools.ls tools/baseTypeCheck.ls tools/doc.ls tools/genLR1.ls tools/prettycompilerfront.ls tools/profile.ls tools/taulextable.ls tools/frontcmd.ls tools/wordgraph.ls"
part1="built/stdlib.lib"
libsrcargs="stdlib libsrc $parts3 uses=common stdlib exports=baseTypeCheck doc genLR1 profile taulextable tools uniqueids wordgraph o=tools.libsrc"
compileargs="common common built/tools.libsrc built/stdlib.libinfo built/common.libinfo"
dependlibs="built/stdlib.$libtype built/common.$libtype"
ccode="void init_common(); void init_stdlib(); void init_libs(){init_stdlib(); init_common();"
makelibrary tools

parts3="built/core.libsrc built/webassembly.lib webcore/inputoutput.ls webcore/webIO.ls common/barycenter.ls common/layergraph.ls common/makeDAG.ls common/bandeskopf.ls stdlib/tausupport.ls stdlib/bitstream.ls stdlib/bitcast.ls stdlib/taublockseq.ls stdlib/ptr.ls stdlib/file.ls"
node="built/webcore.libsrc"
part1="built/stdlib.lib"
(libexeAll stdlib libsrc $parts3 o=webcore.libsrc)
#________________

parts3="built/stdlib.libsrc"
node="built/baseTypeCheck.html"
part1="built/tools.lib"
(libexeAll tools front $parts3 out=baseTypeCheck o=baseTypeCheck.html)

parts3="built/tools.libsrc built/stdlib.libinfo built/common.libinfo"
node="built/callgraphwithin.html"
part1="built/tools.lib"
(libexeAll tools front $parts3 mods=taulextable o=callgraphwithin.html)

parts3="built/common.libsrc"
node="built/commondoc.html"
part1="built/tools.lib"
(libexeAll tools doclibrary $parts3 o=commondoc.html)

parts3="tools/install.txt"
node="built/installdoc.html"
part1="built/tools.lib"
(libexeAll tools formatdoc $parts3 o=installdoc.html)

parts3="built/stdlib.libsrc"
node="built/stdlibdoc.html"
part1="built/tools.lib"
(libexeAll tools doclibrary $parts3 o=stdlibdoc.html)

parts3="tools/doc.txt"
node="built/taudoc.html"
part1="built/tools.lib"
(libexeAll tools formatdoc $parts3 o=taudoc.html)

parts3="stdlib/parse.ls"
node="built/taugrammer.html"
part1="built/tools.lib"
(libexeAll tools LR1 $parts3 o=taugrammer.html)

parts3="tools/install.txt"
node="built/taulex.html"
part1="built/tools.lib"
(libexeAll tools lextable $parts3 o=taulex.html)

parts3="built/webcore.libsrc wbeizer/Bcubic.html wbeizer/Bquadratic.html wbeizer/wbeizer.ls"
node="built/wbeizer.wasm"
part1="built/webassembly.lib"
(libexeAll webassembly wasm $parts3 exports=wbeizer Library=wbeizer o=wbeizer.wasm)

parts3="built/webcore.libsrc built/compilerfront.libsrc built/tools.libsrc built/tests.libsrc webtools/webtools.ls webtools/main2.ls webtools/webtools.html common/svg2graph.ls common/uniqueids.ls stdlib/hashset.ls stdlib/symbol2.ls stdlib/pretty.ls stdlib/symbolconstant.ls stdlib/compileTimeT.ls stdlib/debuginfo.ls stdlib/objectio.ls stdlib/object01.ls stdlib/LEBencoding.ls"
node="built/webtools.wasm"
part1="built/webassembly.lib"
(libexeAll webassembly wasm $parts3 exports=webtools Library=webtools o=webtools.wasm)
#________________
mkbuild 