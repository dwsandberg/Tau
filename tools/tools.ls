#!/bin/sh tau stdlib tools front -out pretty -library tools #

#!/bin/sh tau stdlib tools front -pass text -n getbytefile2 getfile2  -library  stdlib #

#!/bin/sh tau stdlib tools entry  -proc  tools/entrycmd tools/frontcmd tools/tools #

#!/bin/sh tau stdlib tools front -pass text -~n tobyte  -library  stdlib  -mods format textio inputoutput   #

#!/bin/sh tau stdlib tools callgraphbetween -l stdlib standard inputoutput


#!/bin/sh tau stdlib tools callgraphwithin -l webcore  format textio inputoutput   #


#!/bin/sh tau stdlib tools taugrammarpretty

#!/bin/sh tau stdlib tools taugrammar

#!/bin/sh tau stdlib tools lextable

#!/bin/sh tau stdlib tools testprofile  simpletest

#!/bin/sh tau stdlib tools htmlcode  simpletest

#!/bin/sh tau stdlib tools doclibrary  simpletest

#!/bin/sh tau stdlib tools checkTypes -result stdlib #


Module tools

Library tools bandeskopf barycenter baseTypeCheck doc genLR1 layergraph makeDag prettycompilerfront profile svg2graph taulextable
parseargs
frontcmd
entrycmd
uses stdlib
exports baseTypeCheck doc genLR1 profile taulextable tools uniqueids wordgraph

* STATE builtin:profile profileinfo profileresult

* only document printbitcodes profile prettylib doc

* usegraph exclude standard seq set otherseq UTF8 real graph

use UTF8

use format

use frontcmd

use compilerfront

use doc

use genLR1

use main2

use pretty

use prettycompilerfront

use profile

use standard

use taulextable

use seq.char

use seq.word

use process.seq.word

use seq.seq.word

use entrycmd

Function testprofile(libname:seq.word)seq.word subcompilelib.libname + profileresults."time"

Function entrypoint(argin:UTF8)UTF8
{This function was generated from the documentation in the files:' tools/entrycmd tools/frontcmd tools/tools '. Manually 
editing this function is a bad idea.}
let allargs = towords.argin
let cmd = [first.allargs]
let otherargs = allargs << 1
HTMLformat.if cmd = "entry"then
 let args = 
  parseargs(otherargs
  , "main web proc doc option types"
  , "words boolean boolean boolean words words"
  )
 entry(getarg(args, "main"_1)
 , getarg:boolean(args, "web"_1)
 , getarg:boolean(args, "proc"_1)
 , getarg:boolean(args, "doc"_1)
 , getarg(args, "option"_1)
 , getarg(args, "types"_1)
 )
else if cmd = "front"then
 let args = 
  parseargs(otherargs, "library pass n ~n mods ~mods out", "word word words words words words word")
 frontcmd(getarg(args, "library"_1)
 , getarg(args, "pass"_1)
 , getarg(args, "n"_1)
 , getarg(args, "~n"_1)
 , getarg(args, "mods"_1)
 , getarg(args, "~mods"_1)
 , getarg(args, "out"_1)
 )
else if cmd = "pretty"then
 let args = parseargs(otherargs, "library target", "word word")
 prettybyfile(getarg(args, "library"_1), getarg(args, "target"_1))
else if cmd = "lextable"then getlextable
else if cmd = "taugrammar"then gentau
else if cmd = "taugrammarpretty"then gentaupretty
else if cmd = "createdoc"then createdoc
else if cmd = "doclibrary"then
 let args = parseargs(otherargs, "main", "word")
 doclibrary.getarg(args, "main"_1)
else if cmd = "callgraphwithin"then
 let args = parseargs(otherargs, "l main", "word words")
 callgraphwithin(getarg(args, "l"_1), getarg(args, "main"_1))
else if cmd = "callgraphbetween"then
 let args = parseargs(otherargs, "l main", "word words")
 callgraphbetween(getarg(args, "l"_1), getarg(args, "main"_1))
else if cmd = "test3"then
 let args = parseargs(otherargs, "main", "word")
 test3.getarg(args, "main"_1)
else if cmd = "htmlcode"then
 let args = parseargs(otherargs, "main", "word")
 htmlcode.getarg(args, "main"_1)
else if cmd = "testprofile"then
 let args = parseargs(otherargs, "main", "word")
 testprofile.getarg(args, "main"_1)
else if cmd = "createdoc"then createdoc else"unknown command" + cmd

function callgraphwithin(libname:seq.word, args:seq.word)seq.word
callgraphwithin(prg.compilerfront("text", libname), args)

function callgraphbetween(libname:seq.word, args:seq.word)seq.word
callgraphbetween(prg.compilerfront("text", libname), args)

Function test3(lib:seq.word)seq.word
totext(compilerfront("text", lib)
, "tmp"
, [rename("seq.T:findelement(T, seq.T)seq.T", "lookup", [2, 1])
, rename("set.symdef:findelement(symdef, set.symdef)set.symdef", "lookup", [2, 1])
, rename("set.passtypes:findelement(passtypes, set.passtypes)set.passtypes"
, "lookup"
, [2, 1]
)
, rename("set.passsymbols:findelement(passsymbols, set.passsymbols)set.passsymbols"
, "lookup"
, [2, 1]
)
, rename("set.typeentry:findelement(typeentry, set.typeentry)set.typeentry"
, "lookup"
, [2, 1]
)
]
)

use otherseq.word

use parseargs

Function frontcmd(library:seq.word, pass:seq.word, n:seq.word, ~n:seq.word, mods:seq.word
, ~mods:seq.word, out:seq.word)seq.word
if out = "pretty"then
 {should be able to specify target}totext(compilerfront("text", library), "tmp")
else
 front(compilerfront(if isempty.pass then"pass2"else pass, library)
 , pass
 , n
 , ~n
 , mods
 , ~mods
 , out
 )

 /< command -f prettybyfile pretty  /> pretty

 /< option -t word library  /> <library name>

 /< option -t word target  /> <directory to result files in>

/< command -f getlextable lextable /> 

/< command -f gentau taugrammar  /> Grammar used in  tau compiler
 
/< command -f gentaupretty taugrammarpretty  />

/< command -f createdoc createdoc  />

/< command -f doclibrary   doclibrary  /> 
 
/< option -t  word main  /> <library name>


/< command   callgraphwithin  /> 
 
/< option -t word l  /> <library name>

/< option -t words main />  <spec>

/< command    callgraphbetween /> 
 
/< option -t word l  /> <library name>

/< option -t words main />  <spec>

/< command test3    /> 
 
/< option -t word main  /> <library name>
  
/< command htmlcode     /> 
  
   /< option -t word main  /> <library name>
 
  /< command   testprofile />
 
  /< option -t word main  /> <library name>
  
/< command createdoc    /> 

 /< noformat <style> span.command{color:black ; font-size:120%; font-weight:bold;}span.block{padding:0px 0px 0px 
0px ; margin:0px 0px 0px 20px ; display:block ;}span.option{color:blue ;}</style>  /> 
