Module tools

* STATE builtin:profile profileinfo profileresult

* only document printbitcodes profile prettylib doc

* usegraph exclude standard seq set otherseq UTF8 real graph

use UTF8

use IO2

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

Function writeModule(modtexts:seq.seq.word, directory:seq.word)seq.word
{OPTION INLINE}
for txt = "", modtext = "", p ∈ modtexts << 1 + "Module"do
 if not.isempty.p ∧ first.p ∈ "Module module"then
  let discard2 = 
   if isempty.modtext then 0
   else
    createfile([merge(directory + "/" + modtext_2 + ".ls")], toseqbyte.textformat.modtext)
  next(txt + modtext, p)
 else next(txt, modtext + " /p" + p)
/for(txt)

Function entrypoint(argin2:UTF8)UTF8
let argsin = towords.argin2
let cmd = [first.argsin]
let args = [argsin]
let aa=argsin << 1
let idx = findindex("="_1, aa ) 
let rest =if idx > length.aa  then "" else aa << (idx-2)
 let parts=subseq(aa,1,length.aa-length.rest)
{
let parts = extractValue(args, "in")}
let file = getfile:byte(subseq(parts, 1, 3))
HTMLformat.if cmd = "doclibrary"then doclibrary.breakparagraph.file
else if cmd = "pretty"then
 {Pretty print the source code of a Library. The syntax is checked but not the semantics. }
 let target = extractValue(args, "target")
 let a = prettyfile2(true, "", breakparagraph.file)
 writeModule(prettyfile2(true, "", breakparagraph.file)
 , if isempty.target then"tmp"else target
 )
else if cmd = "transform"then
 {Will parse and check the sematics of a library and place one file for each module in the target directory. Expressions such 
as not(a=b)will be rewritten as a /ne b. Modules can be renamed. Example rename=oldname > newname}
 let target = extractValue(args, "target")
 let rename = extractValue(args, "rename")
 let cinfo = compilerfront("text", breakparagraph.file)
 let library = [libname.cinfo]
 let newlib = if isempty.target then"tmp"else target
 writeModule(transform(cinfo
 , newlib
 , if isempty.rename then library + ">" + newlib else rename
 )
 , newlib
 )
else if cmd = "testprofile"then
 let discard = compile.breakparagraph.file
 profileresults."time"
else if cmd = "htmlcode"then htmlcode.breakparagraph.file
else if cmd = "usegraph"then
 let usegraph = usegraph(breakparagraph.file, "mod"_1)
 drawgraph(usegraph
 , asset.extractValue(args, "include")
 , asset.extractValue(args, "exclude")
 )
else if cmd = "formatdoc"then prettyfile(false, "", breakparagraph.file)
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
else if cmd = "lextable"then getlextable
else if cmd = "LR1"then
 LR1gen(breakparagraph.file
 , first."codeonly" ∈ extractValue(args, "flags")
 , first."parameterized" ∈ extractValue(args, "flags")
 )
else"unknown new cmd" + cmd

{Will parse and check the sematics of a library and place one file for each module in the target directory. Expressions such 
as not(a=b)will be rewritten as a /ne b. Modules can be renamed. Example rename=oldname > newname} 