Module tau?

use standard

use textio

use file

use seq.file

use newPretty

use functionHeader

use UTF8

use otherseq.seq.word

use otherseq.word

type helpinfo is cmd:word, exe:word, txt:seq.word

use seq.filename

use seq.char

function %%(s:seq.file) seq.word
for acc = "", lastdir = 1#"built", lastext = 1#"?", e ∈ s
do
 let a = fn.e
 let dir = encodeword(decodeword.dirpath.a << 2),
 next(
  acc
   + (if lastdir = dir then "" else "+" + dir)
   + name.a
   + if lastext = ext.a then "" else "." + ext.a
  , dir
  , ext.a
 ),
acc

Function buildhelp(input:seq.file) seq.word
{COMMAND /strong buildhelp update helpdata in module. 
/br First file in input is module to update. Remaining files are files from which to extract the
help data.}
for acc = empty:seq.seq.word, f ∈ input << 1
do
 for acc3 = acc, e ∈ getHeaders(breakparagraph.[f], true)
 do
  acc3
   + ("/p" + 2#header.e + name.fn.f + escapeformat + header.e << 2 + escapeformat),
 acc3
for
 txt = "function helpdata seq.helpinfo
 /br {This function was created using
 /br buildhelp^(%%.input)}
 /br ["
 , e ∈ alphasort.acc
do
 txt
  + "helpinfo (1#^(dq.[2#e]), 1#^(dq.[3#e]),^(dq.escapedq(e << 3))), /br"
let newdata = txt >> 2 + "]"
for txt2 = "", p ∈ breakparagraph.[1#input]
do
 txt2
  + 
  if subseq(p, 1, 2) = "function helpdata" then
  newdata + "/p"
  else if 1#p ∈ "function Function" then
  pretty.p + "/p"
  else p + "/p",
txt2

function escapedq(s:seq.word) seq.word
for acc = "", e ∈ s do if e ∈ dq then acc + "^(" + "dq)" else acc + e,
acc

Function tau?(cmd:seq.word, out:seq.word) seq.word
{COMMAND /strong tau? Help documentation for commands. This information is extracted from the
comment in the source code for the command.
/br /strong out format of output. if no option is supplied a description of the commands are
printed <* block
/br /strong shellscript creates a shell script for commands.
/br /strong full Full documentations of commands
/br /strong brief Show extract of documentations *>
/br /strong cmd restrict what is displayed. 
/br" cmd = help1" will display documentation for tau? only and" cmd = help1 out" will display
only the documentation of the out option of the tau? command. }
let cmd0 = subseq(cmd, 1, 1)
let option = subseq(cmd, 2, 2),
if out = "shellscript" then
 for acc = "", p ∈ helpdata
 do
  let i = findindex(txt.p, 1#":")
  let defaultDir = if subseq(txt.p, i - 1, i - 1) = "input" then "+built" else "",
  acc + "/br function^(cmd.p) {/br tau^(exe.p)^(cmd.p)^(defaultDir) $@ /br}",
  "#functions are used instead of alias because alias add extra arguments
  /br"
   + acc
else
 for acc = "", c = 1, p ∈ helpdata
 do next(if isempty.cmd0 ∨ cmd.p ∈ cmd0 then acc + hh(p, out, option) + "/br" else acc, c + 1),
  if isempty.out then
   "For more information of command use tau? cmd = <command> out = full
   /br"
    + acc
  else acc

function paradesc(d:helpinfo) seq.word
for acc2 = "", last = 1#"X", w ∈ txt.d
while w ∉ "{}"
do next(if w ∈ ":" then acc2 + last + "," else acc2, w),
if isempty.acc2 then "" else "(^(acc2))"

function hh(d:helpinfo, level:seq.word, option:seq.word) seq.word
if level = "full" then
let j = findindex(txt.d, 1#"COMMAND"), header.d + subseq(txt.d, j + 1, n.txt.d - 1)
else
 let a = cmddesc.1#getHeaders(["Function^(cmd.d)" + txt.d], false),
  if level = "summary" then
   let x = break(a, "<* /br *>", true)
   for acc = "", opt = "", nest = 0, l ∈ x
   do
    if l ∈ ["/br", ""] then
    next(acc, opt, nest)
    else if l = "<* block" then
    next(acc + l, opt, nest + 1)
    else if l = "*>" then
    next(acc + l, opt, nest - 1)
    else
     let newopt = if nest = 0 then [3#l] else opt
     let br = if isempty.acc ∨ 1^acc ∈ "block *>" then "" else "/br"
     let add = if isempty.option ∨ newopt = option then br + "/strong" + l << (2 - nest) else "",
     next(acc + add, newopt, nest),
   header.d + acc
  else "/strong^(cmd.d)" + 2#break(a, "/br", true) << 3

function header(d:helpinfo) seq.word
"/tag <h3> /sp Command /strong^(cmd.d) /sp /tag </h3>"

use seq.headerType

use set.word

use UTF8

use seq.helpinfo

function helpdata seq.helpinfo
{This function was created using
buildhelp+tools tau?.ls+built tools.libsrc stdlib webassembly}
[helpinfo (1#" PEGdebug", 1#" tools"," (input:seq.file, steps:seq.word, notable:boolean) seq.word {COMMAND doc Displays trace of running a PEG. /br-/strong input Expected first paragraph of input to be input and second paragraph to be the grammar /br-/strong steps /em from:/em to. Only display steps between /em from to /em to./br-/strong notable. Do not display parse table or grammar.}"),
helpinfo (1#" buildhelp", 1#" tools"," (input:seq.file) seq.word {COMMAND /strong buildhelp update helpdata in module. /br First file in input is module to update. Remaining files are files from which to extract the help data.}"),
helpinfo (1#" cat", 1#" webassembly"," (files:seq.file, uses:seq.word, exports:seq.word, Library:seq.word) seq.file {COMMAND is this used ?}"),
helpinfo (1#" cmd2html", 1#" stdlib"," (input:seq.file, libname:seq.word, o:seq.word) seq.file {COMMAND}"),
helpinfo (1#" docsource", 1#" tools"," (input:seq.file, cmd:boolean, o:seq.word) seq.file {COMMAND /strong docsource create summary documentation for source code /br The option /strong cmd extracts just the command documentation}"),
helpinfo (1#" entrypoint", 1#" stdlib"," (input:seq.file, entryUses:seq.word) seq.word {COMMAND /strong entrypoint For seeing the package the compiler generates to define the entry point. /br Options:/br /strong entryUses addition use clause added to module when building entry point. }"),
helpinfo (1#" front", 1#" tools",":T (input:seq.file, o:seq.word, pass:seq.word, n:seq.word, ~n:seq.word, mods:seq.word, ~mods:seq.word, within:boolean, out:seq.word) seq.file {COMMAND The /strong front is a multiple purpose command. It outputs data from various stages of the compiler. /p One use is to figure out what functions are used between modules. The usegraph of the core functions indicates there are dependences between the modules texio, file and bits. To see the dependences use <* block front+built stdlib.libsrc mods = textio file bits format *> A graph will be display with the dependences between the modules. The nodes in the graph are the procedure names. Since a name does not uniquely identify a function hovering over the beginning of the name will pop up a more complete discription beginning with the name of the function. /p The dependence on the module bits will not be displayed. If an earilier pass of the compiler is specified like this <* block front  +built stdlib.libsrc mods = textio file bits format pass = text *> then it will be displayed. /p The dependence with in the module textio can be seen with <* block front  +built stdlib.libsrc mods = textio pass = text within = *> /p To see all the functions that call functions named /em breakparagraph in the library use <* block front  +built stdlib.libsrc n = breakparagraph pass = text out = calledby *> /p This will list the function definitions in a package <* block front  +built stdlib.libsrc mods = textio out = symdef *> The format is the function followed by a post order transversal of the call tree. /p The front command takes several parameters that control which functions are considered./br ○ /strong n a list of names of functions to include /br ○ /strong ~n a list of names to exclude /br ○ /strong mods a list of modules to include /br ○ /strong ~mods a list of modules to exculde /br ○ /strong pass The option pass determines how much processing is done before looking at the symbols. <* block • /strong library Only report on functions imported from libraries./br • /strong text Parse the input in such a way that the source code can be reconstructed./br • /strong pass1 Output from first stage of processing. All bindings of text to symbols have been done./br • /strong pass1a Like pass1 with Compiler options on Export statements added. /br • /strong pass2 After some optimization /br • /strong all Just before code generation. *> /br ○ /strong out The option out determines what will be output. <* block • /strong sym Just the symbol names /br • /strong symdef The symbol definitions. The format is the symbol followed by a post order transversal of the call tree./br • /strong symdefgraph For each symbol definition, the definition is presented as a call tree graph./br • /strong calledby The option n is ignored in building a call graph. Then only the symbols that • call symbols in n directly or indirectly are included in the graph /br • /strong calls The option n is ignored in building a call graph. Then only the symbols that • are called (directly or indirectly) from symbols in n are included in the graph./br • /strong txt Instead of producing a SVG graph print the args of the graph./br • /strong baseTypeCheck /br • /strong resultCheck *>}"),
helpinfo (1#" libsrc", 1#" stdlib"," (input:seq.file, uses:seq.word, exports:seq.word, o:seq.word) seq.file {COMMAND /strong libsrc Is this being used?}"),
helpinfo (1#" makeScript", 1#" stdlib"," (input:seq.file, o:seq.word, builddir:seq.word, debug:boolean, hashes:seq.file) seq.word {COMMAND /strong makeScript creates shell script for building code}"),
helpinfo (1#" makebitcode", 1#" stdlib"," (input:seq.file, libname:seq.word, exports:seq.word, uses:seq.word, info:boolean, profile:boolean, showllvm:seq.word, entryUses:seq.word) seq.file {OPTION COMMAND /strong makebitcode compiler /br Options:/br /strong entryUses addition use clause added to module when building entry point. /br /strong profile generates information for profiling /br /strong showllvm /br /info /br /uses /br /exports /br /libname}"),
helpinfo (1#" prettystate", 1#" stdlib"," (input:seq.file, o:seq.word) seq.word {COMMAND ???}"),
helpinfo (1#" tau?", 1#" tools"," (cmd:seq.word, out:seq.word) seq.word {COMMAND /strong tau? Help documentation for commands. This information is extracted from the comment in the source code for the command./br /strong out format of output. if no option is supplied a description of the commands are printed <* block /br /strong shellscript creates a shell script for commands./br /strong full Full documentations of commands /br /strong brief Show extract of documentations *> /br /strong cmd restrict what is displayed. /br^(dq) cmd = help1^(dq) will display documentation for tau? only and^(dq) cmd = help1 out^(dq) will display only the documentation of the out option of the tau? command. }"),
helpinfo (1#" transform", 1#" tools",":T (input:seq.file, o:seq.word, target:seq.word, modrename:seq.word, bind:boolean, reorguse:boolean, html:seq.word, cleanexports:boolean, moveexports:boolean, patternmods:seq.word) seq.file {COMMAND The /strong transform cmd takes a list of input source files. For each module in the input a pretty printed file is in the directory <Tau>/tmp Addition parameters allows for different variants. <* block transform helloworld/helloworld.ls /br transform helloworld/helloworld.ls reorguse = /br transform  +built HelloWorld.libsrc	 stdlib.libinfo bind = /br transform  +built HelloWorld.libsrc	 stdlib.libinfo bind = reorguse = *> /p This first variant does not require the source to be sematicaly correct but the syntax must be correct. It does not change the order of the paragraphs. /p The second is like the first except that it moves the use paragraphs to the beginning of the module, removes duplicates, and sorts them./p The third is like the first but requires correct semantics. This allows some additional transformations such as^(dq) not (a = b)^(dq) to become^(dq) a /ne b^(dq) /br ○ /strong target overides default target directory tmp /br ○ /strong bind Does further processing of input to bind id's to symbols./br ○ /strong reorguse Reorganizes use clauses. If /em bind is also specified unnecessary use clauses are removed./br ○ /strong html An html file is produced with an index of modules. This option is useful for examining source code Useful for producing documentation with imbedded Tau code./br ○ /strong modrename List of modules to rename in form: oldname1 newname1 oldname2 newname2... /p The /keyword transform command treats the function genEnum as magic and will generate code in a module for enumeration types instead of creating the code by hand. /tag <a /sp a href =^(dq)#enum^(dq) > Example /tag </a>}"),
helpinfo (1#" unusedsymbols", 1#" tools",":T (input:seq.file, o:seq.word, all:boolean, generated:boolean, excessExports:boolean, ignore:seq.word) seq.file {COMMAND The /strong unusedsymbols cmd analyzes code for unused functions. It forms the function call graph for the program. /br It then looks for any any sources in the call graph that are not the entry point of the program and lists them. Any functions that are generated from type definitions are also removed. /p Here is an example <* block tau tools unusedsymbols+built tools.libsrc stdlib.libinfo common *> /p The behavior can be modified with flags. /br • /strong all list all unused functions--not just the roots. /br • /strong generated the symbols generated from type definitions are included. /br • /strong excessExports list symbols exported from a module but only used internally to that module./br • /strong ignore Symbols with these names are not listed in output. Default value is genEnum genPEG}"),
helpinfo (1#" updatestate2", 1#" stdlib"," (input:seq.file, o:seq.word, builddir:seq.word, debug:boolean, hashes:seq.file) seq.file {COMMAND doc not finished}"),
helpinfo (1#" usegraph", 1#" tools"," (input:seq.file, include:seq.word, exclude:seq.word) seq.word {COMMAND /strong usegraph graphs /em use releationshhip between modules in source code. /br /br options: /br /strong exclude lists the modules to ignore in the use clauses. /br /strong include restricts the modules considered to those listed./p Examples:<* block > usegraph /sp+built core.libsrc /tag <a /sp href =^(dq)../documentation/Ex1usegraph.html^(dq) > Result /tag </a> /sp /br > usegraph /sp+built core.libsrc exclude = seq standard /tag <a /sp href =^(dq)../documentation/Ex2usegraph.html^(dq) > Result /tag </a> /sp /br > usegraph /sp+built core.libsrc include = UTF8 words standard textio exclude = seq standard /tag <a /sp href =^(dq)../documentation/Ex3usegraph.html^(dq) > Result /tag </a> /sp /br > usegraph /sp+core UTF8.ls textio words standard encoding xxhash exclude = seq standard *> /p The last two examples give the same result. The first excludes modules from consideration and the second only includes source files of modules that should be included. }"),
helpinfo (1#" wasm", 1#" webassembly"," (input:seq.file, Library:seq.word, exports:seq.word, o:seq.word, info:boolean, profile:boolean) seq.file {COMMAND problem is same symbol is used in different onclicks}")]

 