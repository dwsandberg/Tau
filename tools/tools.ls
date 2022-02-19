#!/bin/sh tau stdlib tools pretty -library   tools  -target tmp #


#!/bin/sh tau stdlib tools genep  tools #

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
uses stdlib
exports baseTypeCheck doc genLR1 profile taulextable tools uniqueids wordgraph

* STATE builtin:profile profileinfo profileresult

* only document printbitcodes profile prettylib doc

* usegraph exclude standard seq set otherseq UTF8 real graph

use UTF8

use format

use baseTypeCheck

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

Function testprofile(libname:seq.word)seq.word subcompilelib.libname + profileresults."time"

Function entrypoint(argin:UTF8)UTF8 
let allargs = towords.argin 
let cmd = [first.allargs] 
let otherargs = allargs << 1 
HTMLformat.if cmd = "pretty" then
let args = parseargs(otherargs, "library target" , "word word" ) 
prettybyfile(getarg(args, "library" _1), getarg(args, "target" _1))
else if cmd = "genep" then
let args = parseargs(otherargs, "main web" , "words boolean" ) 
genentrypoint(getarg(args, "main" _1), getarg:boolean(args, "web" _1))
else if cmd = "lextable" then getlextable 
else if cmd = "taugrammar" then gentau 
else if cmd = "taugrammarpretty" then gentaupretty 
else if cmd = "createdoc" then createdoc 
else if cmd = "doclibrary" then
let args = parseargs(otherargs, "main" , "word" ) 
doclibrary.getarg(args, "main" _1)
else if cmd = "checkTypes" then
let args = parseargs(otherargs, "main result" , "word boolean" ) 
glue(getarg(args, "main" _1), getarg:boolean(args, "result" _1))
else if cmd = "callgraphwithin" then
let args = parseargs(otherargs, "l main" , "word words" ) 
callgraphwithin(getarg(args, "l" _1), getarg(args, "main" _1))
else if cmd = "callgraphbetween" then
let args = parseargs(otherargs, "l main" , "word words" ) 
callgraphbetween(getarg(args, "l" _1), getarg(args, "main" _1))
else if cmd = "test3" then
let args = parseargs(otherargs, "main" , "word" ) 
test3.getarg(args, "main" _1)
else if cmd = "htmlcode" then
let args = parseargs(otherargs, "main" , "word" ) 
htmlcode.getarg(args, "main" _1)
else if cmd = "testprofile" then
let args = parseargs(otherargs, "main" , "word" ) 
testprofile.getarg(args, "main" _1)
else if cmd = "createdoc" then createdoc else "unknown command" + cmd
 
function callgraphwithin(libname:seq.word, args:seq.word) seq.word
  callgraphwithin(prg.compilerfront("text",  libname ), args)

function callgraphbetween(libname:seq.word, args:seq.word) seq.word
  callgraphbetween(prg.compilerfront("text",  libname ), args)


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

use  otherseq.word

function glue(library:seq.word, basetypecheck:boolean)seq.word
let r2 = compilerfront("pass2", library)
if basetypecheck then baseTypeCheck.r2 else checkresults.prg.r2 

function clean(p:seq.word, add:seq.word)seq.word
let i = findindex(first." />", p)
" /p"
+ if p_2 ∉ "option"then subseq(p, 1, 2) + subseq(p, i - 1, length.p)
else
 " /< block" + subseq(p, 1, 2) + "-" + subseq(p, i - 1, length.p)
 + " />"
 
 function quote(s:seq.word)seq.word '"' + s + '"'
 
 use textio
 
 use seq.cmdinfo
 
type cmdinfo is parano:int,cmdname:word,proc:seq.word,types:seq.word,options:seq.word

Function genentrypoint(libname:seq.word,html:boolean)seq.word
let functionheader=if html then 
' Function runcmd(id0:jsbytes) int
let cmd=towords.id0
setElementValue("pageready", '
else "Function entrypoint(argin:UTF8)UTF8 let allargs=towords.argin let cmd=[first.allargs]let otherargs=allargs 
<< 1 HTMLformat("
let desc2 = gettext([first.libname] + "/" + first.libname + ".ls")
let desc = 
 for idx = 1, p ∈ desc2 while" /< command" ≠ subseq(p, 1, 2)do idx + 1 /for(subseq(desc2, idx, length.desc2))
let cmds=
for acc=empty:seq.cmdinfo,idx=1,lastcmd=0,options=""
, p ∈ desc+ "/< command a a />"
do
 let key = subseq(p, 1, 2)
 if key = " /< command"then 
  if lastcmd=0 then next(acc,idx+1,idx,"")
  else 
   let argtypes = reverse( options >> (length.options / 2))
  let validargs = options << (length.options / 2)
  let t=desc_lastcmd
   let new=cmdinfo(lastcmd,t_4,[t_3],argtypes,validargs)
     next(acc+new,idx+1,idx,"")
 else if key = " /< option"then next(acc,idx+1,lastcmd, [p_3] + options + p_4)
 else next(acc,idx+1,lastcmd, options)
 /for(acc)
{ for txt="",c /in cmds do 
   txt+"/br"+cmdname.c+proc.c+options.c+types.c
/for(txt)}
let doc=for txt = " /< noformat <h1>" + first.libname + "Command Documentation </h1>  />"
, cmdno=1,p ∈ desc
do
 let key = subseq(p, 1, 2)
 if key = " /< command"then 
 let new= clean(p, "") +
   if html /and not.isempty.options.cmds_cmdno then
      "/< noformat <input id=" +merge([cmdname.cmds_cmdno]+"$"+space +"/>")+ "/>" else "" /if
   +if html then 
   "/< noformat <button id=" +cmdname.cmds_cmdno +"onclick=runcmd(jsstring2UTF8bytes(this.id)) >run cmd </button> />" 
   else "" 
  next(txt+new,cmdno+1)
 else if key = " /< option"then  next(txt + clean(p, "-"),cmdno)
  else next(txt + " /p" + p,cmdno)
/for(txt)
let proc=" /< noformat <h2> Entry point procedure </h1>  />"
+  pretty .
for txt = ""
,c ∈ cmds
do
    let args = 
     if isempty.options.c then""
     else
      for txt2 = "(", idx = 1, a ∈ options.c do
        let cc= if (types.c)_idx /in "boolean" then "getarg:boolean(args,"
        else "getarg(args, "
       next(txt2 + cc + quote.[a] + "_1), ", idx + 1)
      /for(txt2 >> 1 + ")")
    txt+"if cmd=" + quote.[cmdname.c] + "then" + 
    if isempty.args  then "" else 
     if html then 
     "let otherargs=getElementValue."+merge([cmdname.c]+"$")
     else "" /if 
     +"let args=parseargs(otherargs, "
    + quote.options.c
    + ", "
    + quote.types.c
    + ")" /if
    + proc.c
    + args
    + "else"
/for(functionheader+
txt
+ '"unknown command"+cmd )')
doc+proc

   use parseargs
    
function prettybyfile(libname:seq.word, targetdir:seq.word)seq.word
{OPTION INLINE}
let filelist = first.extractinfo.gettext(libname + "/" + libname + ".ls") << 1
for acc = "", file ∈ filelist do
 let chars = decodeword.file
 let getname = 
  if chars_1 = char1."/"then[encodeword(chars << 1)] + ".ls"
  else libname + "/" + file + ".ls"
 let z = prettyfile(true, "", gettext.getname)
 let discard = createfile(outname(file, targetdir), toseqbyte.textformat.z)
 acc + for txt = "", @e ∈ z do txt + " /p" + @e /for(txt)
/for(acc)

function outname(file:word, targetdir:seq.word)seq.word
let chars = decodeword.file
if chars_1 = char1."/"then
 targetdir + "/" + encodeword(chars << (findindex(char1."/", chars << 1) + 1))
 + ".ls"
else targetdir + "/" + file + ".ls"

function textformat(p:seq.seq.word)UTF8
for txt = "", @e ∈ p do txt + " /p" + @e /for(textformat(txt << 1))

use libraryModule

use otherseq.char


 /< command prettybyfile pretty  /> pretty

 /< option word library  /> <library name>

 /< option word target  /> <directory to result files in>

 /< command genentrypoint genep  /> Generates entrypoint procedure from documentation. 

 /< option words main  /> <library name>
 
 /< option boolean web  />  For use in web applications.

/< command getlextable lextable /> 

/< command gentau taugrammar  /> Grammar used in  tau compiler
 
/< command gentaupretty taugrammarpretty  />

/< command createdoc createdoc  />

/< command doclibrary   doclibrary  /> 
 
/< option word main  /> <library name>

/< command glue   checkTypes  /> 
 
/< option word main  /> <library name>

/< option boolean result  /> 

/< command callgraphwithin   callgraphwithin  /> 
 
/< option word l  /> <library name>

/< option words main />  <spec>

/< command callgraphbetween   callgraphbetween /> 
 
/< option word l  /> <library name>

/< option words main />  <spec>


/< command test3   test3  /> 
 
/< option word main  /> <library name>
  
/< command htmlcode   htmlcode  /> 
  
   /< option word main  /> <library name>
 
  /< command testprofile testprofile />
 
  /< option word main  /> <library name>
  
/< command createdoc   createdoc /> 


 /< noformat <style> span.command{color:black ; font-size:120%; font-weight:bold;}span.block{padding:0px 0px 0px 
0px ; margin:0px 0px 0px 20px ; display:block ;}span.option{color:blue ;}</style>  /> 
