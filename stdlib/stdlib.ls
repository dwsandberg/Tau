Library stdlib UTF8 bits bitstream codegennew codetemplates compilerfront encoding 
inputoutput format  graphs/barycenter    graphs/graph   
  graphs/layergraph graphs/makeDAG     internalbc interpreter libdesc libraryModule llvm llvmconstants main2  
mangle mergeblocks mytype otherseq outstream parse parsersupport pass2 passparse passsymbol persistant postbind pretty process real seq set sparseseq stack standard symbol symbol2 symboldict symref tausupport tests/bug7 tests/checking tests/myseq tests/point tests/randomphrase tests/test11 tests/test20 tests/testencoding tests/testfileio tests/testmodules tests/testprocess tests/testseq tests/wordfreq testsCompile/test11a testsCompile/testall testsCompile/testopt textio timestamp tree typedict words xxhash
uses
exports UTF8 bandeskopf barycenter bits dataio display displaygraph displaytextgraph encoding fileio format graph hashset index internalbc ioseq ipair labeledgraph layergraph libraryModule llvm llvmconstants main2 maindict makeDAG mangle otherseq pretty process real seq set sparseseq stack standard svg svggraph 
symbol2 taublockseq tausupport testall textio timestamp tree words xxhash
bitcast




* Removed maindict

* only document standard seq real

Module PROFILE

use bits

use codegennew

use codetemplates

use compilerfront

use libdesc

use main2

use pass2

use passparse

use passsymbol

use standard

use symbol

use seq.bits

use set.passsymbols

use seq.symbol

use set.symbol

Export subcompilelib(seq.word)seq.word

Export pass2(placehold:set.symdef)set.symdef

Export codegen(theprg:set.symdef, uses:set.symbol, thename:word, libdesc:libdescresult, alltypes:typedict, isbase:boolean)seq.bits

Export compilerfront(option:seq.word, libname:seq.word, allsrc:seq.seq.word, dependentlibs:seq.word, exports:seq.word)compileinfo

Export passparse(abstractmods:set.passsymbols, simplemods:set.passsymbols, lib:word, prg1:seq.symdef, src:seq.seq.word, mode:word)set.symdef

Export stepone(theprg:set.symdef, roots:set.symbol, alltypes:typedict, isbase:boolean, thename:word, newmap:set.symbolref)steponeresult

/Export uses(p:program, alltypes:typedict, processed:set.symbol, toprocess:set.symbol, infref:set.symbol, inrecordconstant 
:set.symbol, inother:set.symbol)usesresult

module STATE

use bits

use inputoutput

use standard

use timestamp

use seq.bits

Export currenttime timestamp

/Export getfile(name:cstr)fileresult

/Export getbytefile(cstr)fileresultbyte

/Export getbitfile(cstr)fileresultbit

Export createfile2(byteLength:int, data:seq.bits, cstr)int

module INLINE

use symbol

Export Lit(int)symbol

module NOINLINE

use UTF8

use standard

use symbol

/use inputoutput

/use seq.byte

/use bits

/Export  getfileX:byte(seq.word,int) seq.byte


Export toword(int)word

Export decodeword(word)seq.char

Export encodeword(seq.char)word

module COMPILETIME

use UTF8

use bits

use real

use standard

use tausupport

use typedict

use seq.word

Export-(int)int

Export +(int, int)int

Export-(int, int)int

Export /(int, int)int

Export *(int, int)int

Export =(int, int)boolean

Export =(word, word)boolean

Export =(boolean, boolean)boolean

Export >(int, int)boolean

Export ∧(a:bits, bits)bits

Export ∨(a:bits, bits)bits

Export >>(a:bits, i:int)bits

Export <<(a:bits, i:int)bits

Export-(real, real)real

Export +(seq.word, seq.word)seq.word

Export merge(seq.word)word

Export makereal(seq.word)real

Export getseqlength(ptr)int

Export toword(int)word

Export encodeword(seq.char)word

Export decodeword(word)seq.char

Export char1(seq.word)char

Export_(seq.word, index)word

Export_(seq.word, int)word

Export_(seq.int, int)int

Export_(seq.char, int)char 