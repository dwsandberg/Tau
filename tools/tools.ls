Module tools

* STATE builtin:profile profileinfo profileresult

* only document printbitcodes profile prettylib doc

* usegraph exclude standard seq set otherseq UTF8 real graph

use UTF8

use compilerfront

use doc

use format

use frontcmd

use genLR1

use libraryModule

use main2

use pretty

use prettycompilerfront

use profile

use standard

use taulextable

use textio

use seq.char

use otherseq.word

use seq.word

use set.word

use process.seq.word

use seq.seq.word

use bits

Function writeModule2(modtexts:seq.seq.word, directory:seq.word)seq.file
{OPTION INLINE}
for acc = empty:seq.file, modtext = "", p ∈ modtexts << 1 + "Module" do
 if length.p > 1 ∧ first.p ∈ "Module module"then
   next(if isempty.modtext then acc
   else
    acc+file(filename("+"+directory+modtext_2+".ls"),modtext)
    , p)
 else next(acc, modtext + " /p" + p)
/for(acc)


use file

use seq.file


Function pretty(input:seq.file,o:seq.word,target:seq.word) seq.file
writeModule2(prettyfile2(true, "", breakparagraph.data.first.input)
 , if isempty.target then"tmp"else target
 )

Function formatdoc(input:seq.file,o:seq.word ) seq.file
[file( filename.o,prettyfile(false, "", breakparagraph.data.first.input))]

Function lextable(input:seq.file,o:seq.word ) seq.file
[file( o,getlextable)]

Function LR1(input:seq.file,o:seq.word,codeonly:boolean,parameterized:boolean ) seq.file
[file( o,LR1gen(breakparagraph.data.first.input,codeonly,parameterized) )]

Function front(input:seq.file,o:seq.word
, pass:seq.word, n:seq.word, ~n:seq.word, mods:seq.word
, ~mods:seq.word, within:boolean, rn:seq.word, out:seq.word) seq.file
let output=front(compilerfront(if isempty.pass then"pass2"else pass, breakparagraph.data.first.input)
,pass,n,~n,mods,~mods,within ,rn,out)
[file(o,output)]

Function transform(input:seq.file,o:seq.word,target:seq.word,rename:seq.word) seq.file
{Will parse and check the sematics of a library and place one file for each module in the target directory. Expressions such 
as not(a=b)will be rewritten as a /ne b. Modules can be renamed. Example rename=oldname > newname} let cinfo = compilerfront("text", breakparagraph.data.first.input)
 let library = [libname.cinfo]
 let newlib = if isempty.target then"tmp"else target
 writeModule2(transform(cinfo
 , newlib
 , if isempty.rename then library + ">" + newlib else rename
 )
 , newlib
 )

/Function Xentrypoint(argin2:UTF8)UTF8
let args = towords.argin2
let cmd = [first.args]
let input=getfiles.args
let file = data.first.input
 let out=HTMLformat.if cmd = "testprofile"then
 {let discard = compile.breakparagraph.file
 profileresults."time"}
 "needs work"
else if cmd = "front"then
 let pass = extractValue(args, "pass")
 front(compilerfront(if isempty.pass then"pass2"else pass, breakparagraph.file)
 , pass
 , extractValue(args, "n")
 , extractValue(args, "n!")
 , extractValue(args, "mods")
 , extractValue(args, "mods!")
 , first."within" ∈ extractValue(args, "flags")
 , extractValue(args, "rn")
 , extractValue(args, "out")
 )
else 
else"unknown new cmd" + cmd

