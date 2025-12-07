Module tau?

Implements the tau help command, tau?, and buildhelp for extraction help information from the source.

use UTF8

use seq.char

use file

use seq.file

use seq.filename

use seq.helpinfo

use pretty

use standard

use textio

use token

use seq1.seq.word

use sort.seq.word

use seq1.word

use set.word

use sort.word

use seq.byte

use bits

type helpinfo is cmd:word, exe:word, txt:seq.word

function %%(s:seq.file) seq.word
for acc = "", lastdir = "built" sub 1, lastext = "?" sub 1, e ∈ s
do
 let a = fn.e
 let t = decodeword.dirpath.a,
 let dir =
  if subseq(t, 1, 2) = [char1.".", char1."/"] then encodeword(t << 2) else dirpath.a,
 next(
  acc
  + (if lastdir = dir then "" else "+" + dir)
  + name.a
  + (if lastext = ext.a then "" else "." + ext.a)
  , dir
  , ext.a
 ),
acc

Function buildhelp(
input:seq.file
, target:seq.file
, shellscript:boolean
, doc:boolean
) seq.byte
{COMMAND /strong buildhelp update helpdata in module. /br
/strong input files from which to extract the help data./br
/strong target file to update help data in /br
/strong shellscript produces shell script to define commands./br
/strong doc format for command documentation source file.}
assert shellscript ∨ doc ∨ not.isempty.target report "Target must be specified."
for acc = empty:seq.seq.word, f ∈ input
do
 for acc3 = acc, p ∈ breakparagraph.[f]
 do
  if p sub 1 ∈ "Function" then
   let h = getheader.p
   {Header will include two additional words for formatting keywords Function}
   if subseq(p, n.h - 1, n.h) = "{COMMAND" then
    acc3
    + ([p sub 2]
    + name.fn.f
    + escapeformat
    + subseq(p, 3, findindex(p, "}" sub 1))
    + escapeformat)
   else acc3
  else acc3,
 acc3
for info = empty:seq.helpinfo, e ∈ sort>alpha.acc
do info + helpinfo(e sub 1, e sub 2, e << 2),
if doc then
 let esc = [escapeformat]
 for txt = "", e ∈ info
 do
  let j = findindex(txt.e, "COMMAND" sub 1)
  let jend = findindex(txt.e, "}" sub 1),
  txt + "// Command:(cmd.e)/h3 /p:(subseq(txt.e, j + 1, jend - 1))",
 toseqbyte.processTXT([txt], stdCSS, false, "en")
else if shellscript then toseqbyte.textFormat1a.script.info
else
 let discard = tknencoding
 for
  txt = "function helpdata seq.helpinfo /br
  {This function was created using /br
  buildhelp:(%%.input)target::(%%.target)}/br
  ["
  , e ∈ info
 do
  txt
  + "helpinfo(:(dq.[cmd.e])sub 1,:(dq.[exe.e])sub 1,:(dq.escapedq.txt.e)), /br
  "
 let newdata = txt >> 2 + "]",
 for txt2 = "", p ∈ breakparagraph.[target sub 1]
 do
  if txt2 = "" ∧ subseq(p, 1, 2) = "# File" then txt2
  else
   txt2
   + if subseq(p, 1, 2) = "function helpdata" then newdata + "/p"
   else if p sub 1 ∈ "function Function" then removeMarkup.pretty.p + "/p"
   else p + "/p",
 toseqbyte.textFormat1a.txt2

use markup

function escapedq(s:seq.word) seq.word
for acc = "", e ∈ s do if e ∈ dq then acc + "^" + "(dq)" else acc + e,
acc

Function tau?(cmd:seq.word, %:seq.word) seq.word
{COMMAND /strong tau? Help documentation for commands. /br
This information is extracted from the comment in the source code for the command. If no option is supplied a description of the commands are printed./br
/strong cmd restrict what is displayed. /br
"cmd: help1"will display documentation for tau? only and"cmd: help1 out"will display only the documentation of the out option of the tau? command. /br
Options:<* block /strong % format of output. /br
/strong shellscript creates a shell script for commands./br
/strong full Full documentations of commands /br
/strong brief Show extract of documentations *>}
let cmd0 = subseq(cmd, 1, 1)
let option = subseq(cmd, 2, 2),
if % = "shellscript" then script.helpdata
else
 for acc = "", c = 1, p ∈ helpdata
 do
  next(
   if isempty.cmd0 ∨ cmd.p ∈ cmd0 then acc + hh(p, %, option) + "/br" else acc
   , c + 1
  ),
 if isempty.% then
  "For more information on command use tau? cmd: <command> %: full /br
  :(acc)"
 else acc

function script(s:seq.helpinfo) seq.word
for acc = "", p ∈ s
do
 let i = findindex(txt.p, ":" sub 1)
 let defaultDir = if subseq(txt.p, i - 1, i - 1) = "input" then "+built" else "",
 acc
 + "/br function:(cmd.p){/br
 tau:(exe.p):(cmd.p):(defaultDir)$@ /br
 }",
 "# functions are used instead of alias because alias adds extra arguments /br
:(acc)"

function paradesc(d:helpinfo) seq.word
for acc2 = "", last = "X" sub 1, w ∈ txt.d
while w ∉ "{}"
do next(if w ∈ ":" then acc2 + last + "," else acc2, w),
if isempty.acc2 then "" else "(:(acc2))"

function hh(d:helpinfo, level:seq.word, option:seq.word) seq.word
if level = "full" then
 let j = findindex(txt.d, "COMMAND" sub 1),
 header.d + subseq(txt.d, j + 1, n.txt.d - 1)
else
 let a = "kl",
 "/strong:(cmd.d):(break(a, "/br", true) sub 2 << 3)"

function header(d:helpinfo) seq.word "Command //:(cmd.d)/strong /h3"

function helpdata seq.helpinfo
{This function was created using
buildhelp tools.libsrc taubc webassembly transform1info.html target:+tools tau?.ls}
[helpinfo("PEGdebug"sub 1,"tools"sub 1,"(input:seq.file, steps:seq.word, notable:boolean)seq.word{COMMAND /strong PEGdebug displays a trace of running a PEG. /br-/strong input Expected first paragraph of input to be input and second paragraph to be the grammar./br-/strong steps from to. Only display steps between from and to./br-/strong notable. Do not display the parse table or grammar.}"),
helpinfo("buildhelp"sub 1,"tools"sub 1,"(input:seq.file, target:seq.file, shellscript:boolean, doc:boolean)seq.byte{COMMAND /strong buildhelp update helpdata in module. /br /strong input files from which to extract the help data./br /strong target file to update help data in /br /strong shellscript produces shell script to define commands./br /strong doc format for command documentation source file.}"),
helpinfo("entrypoint"sub 1,"taubc"sub 1,"(input:seq.file, entryUses:seq.word, core:boolean)seq.word{COMMAND /strong entrypoint For seeing the Module the compiler generates to define the entry point. /br Options:/br /strong entryUses addition use clause added to module when building entry point. /br /strong core Only show core of Module. }"),
helpinfo("front"sub 1,"tools"sub 1,":T(input:seq.file, output:seq.word, pass:seq.word, n:seq.word, ~n:seq.word, mods:seq.word, ~mods:seq.word, within:boolean, %:seq.word)seq.file{COMMAND The /strong front is a multiple purpose command. It outputs data from various stages of the compiler. /p One use is to figure out what functions are used between modules. The usegraph of the core functions indicates there are dependences between the modules texio, file and bits. To see the dependences use <* block front /sp+built core.libsrc mods: textio file bits format *> A graph will be display with the dependences between the modules. The nodes in the graph are the procedure names. Since a name does not uniquely identify a function hovering over the beginning of the name will pop up a more complete discription beginning with the name of the function. /p The dependence on the module bits will not be displayed. If an earilier pass of the compiler is specified like this <* block front  +built taubc.libsrc mods = textio file bits format pass = text *> then it will be displayed. /p The dependence with in the module textio can be seen with <* block front  +built taubc.libsrc mods = textio pass = text within = *> /p To see all the functions that call functions named /em breakparagraph in the library use <* block front  +built taubc.libsrc n = breakparagraph pass = text out = calledby *> /p This will list the function definitions in a package <* block front  +built taubc.libsrc mods = textio out = symdef *> The format is the function followed by a post order transversal of the call tree. /p The front command takes several parameters that control which functions are considered./br ○ /strong n a list of names of functions to include /br ○ /strong ~n a list of names to exclude /br ○ /strong mods a list of modules to include /br ○ /strong ~mods a list of modules to exculde /br ○ /strong pass The option pass determines how much processing is done before looking at the symbols. <* block • /strong library Only report on functions imported from libraries. /br • /strong text Parse the input in such a way that the source code can be reconstructed./br • /strong pass1 Output from first stage of processing. All bindings of text to symbols have been done./br • /strong pass1a Like pass1 with Compiler options on Export statements added. /br • /strong pass2 After some optimization /br • /strong all Just before code generation. *> /br ○ /strong % The option % determines the format of the output. <* block • /strong sym Just the symbol names /br • /strong symdef The symbol definitions. The format is the symbol followed by a post order transversal of the call tree./br • /strong symdefgraph For each symbol definition, the definition is presented as a call tree graph./br • /strong calledby The option n is ignored in building a call graph. Then only the symbols that • call symbols in n directly or indirectly are included in the graph /br • /strong calls The option n is ignored in building a call graph. Then only the symbols that • are called(directly or indirectly)from symbols in n are included in the graph./br • /strong txt Instead of producing a SVG graph print the args of the graph./br • /strong baseTypeCheck /br • /strong resultCheck *>}"),
helpinfo("makeScript"sub 1,"taubc"sub 1,"(input:seq.file, builddir:seq.word, hashes:seq.file, output:seq.word)seq.byte{COMMAND /strong makeScript creates shell script for building code./br The commands' primary is is in the shell script taubuild./br /strong input build files /br /strong builddir build directory, usually ^(dq)+built ^(dq)./br /strong hashes two files with one containing lines from the unix command shasum. The two files are compared looking for identical lines which is used to determine which files have not be changed since the last build.}"),
helpinfo("makebitcode"sub 1,"taubc"sub 1,"(input:seq.file, exports:seq.word, info:boolean, profile:boolean, showllvm:seq.word, entryUses:seq.word, output:seq.word)seq.file{COMMAND /strong makebitcode compiler /br Options:/br /strong entryUses addition use clause added to module when building entry point. /br /strong profile generates information for profiling /br /strong showllvm show text form of llvm code generated for the names of procedure given./br /info show text form of code info /br /exports list of packes to show. }"),
helpinfo("prettyScript"sub 1,"tools"sub 1,"(input:seq.file, builddir:seq.word, hashes:seq.file, roots:seq.word, %:seq.word)seq.word{COMMAND /strong prettyScript pretty prints /sp.bld script./br /strong % format of output. <* block /br /strong pretty ? /br /strong full Graph of dependences between files./br /strong outdated like full but only include outdated files in graph /br /strong script shell script for updating without the file hashes. *> /p options used for formats other than pretty./br /strong roots only include the filenames list and their descendants in graph. /br /strong hashes ? /br /strong builddir build target directory. Defaults to ^(dq)+built ^(dq)}"),
helpinfo("tau?"sub 1,"tools"sub 1,"(cmd:seq.word, %:seq.word)seq.word{COMMAND /strong tau? Help documentation for commands. /br This information is extracted from the comment in the source code for the command. If no option is supplied a description of the commands are printed./br /strong cmd restrict what is displayed. /br ^(dq)cmd: help1 ^(dq)will display documentation for tau? only and ^(dq)cmd: help1 out ^(dq)will display only the documentation of the out option of the tau? command. /br Options:<* block /strong % format of output. /br /strong shellscript creates a shell script for commands./br /strong full Full documentations of commands /br /strong brief Show extract of documentations *>}"),
helpinfo("transform"sub 1,"tools"sub 1,":T(input:seq.file, link:seq.file, output:seq.word, target:seq.word, modrename:seq.word, bind:boolean, reorguse:boolean, html:seq.word, cleanexports:boolean, moveexports:boolean, patternmods:seq.word)seq.file{COMMAND The /strong transform cmd takes a list of input source files. For each module in the input a pretty printed file is created in the directory <Tau>/tmp Addition parameters allows for different variants. <* block transform+tests profileExample.ls helloworld.ls /br transform+tests profileExample.ls reorguse:/br transform  +built profileExample.libsrc	 taubc.libinfo bind:/br transform  +built profileExample.libsrc	 taubc.libinfo bind: reorguse: *> /p This first variant does not require the source to be semantically correct but the syntax must be correct. It does not change the order of the paragraphs. /p The second is like the first except that it moves the use paragraphs to the beginning of the module, removes duplicates, and sorts them./p The third is like the first but requires correct semantics. This allows some additional transformations such as ^(dq)not(a = b)^(dq)to become ^(dq)a /ne b ^(dq)/br ○ /strong target overides default target directory tmp /br ○ /strong bind Does further processing of input to bind id's to symbols./br ○ /strong reorguse Reorganizes use clauses. If /em bind is also specified unnecessary use clauses are removed./br ○ /strong link A list of file names ending with /sp.html that will not be compiled but will be scanned for functions that are called by the files. Hyperlinks will be create from the location of the call to the definition in the link files. Files without a.html extenstion are ignored. /br ○ /strong html An html file is produced with an index of modules. This option is useful for examining source code and contains for producing documentation with imbedded Tau code.This options contains one or more of the following. <* block • /strong Module Include modules in the table of contents. /br • /strong headersOnly Only include the headers of exported functions in result./br • /strong h1 include html h1 headers in table of contents /br • /strong h2 include html h2 headers in table of contents /br • /strong h3 include html h3 headers in table of contents /br • /strong h4 include html h4 headers in table of contents /br • /strong h5 include html h5 headers in table of contents /br • /strong h6 include html h6 headers in table of contents *> /br ○ /strong modrename List of modules to rename in form: oldname1 newname1 oldname2 newname2... /br ○ /strong patternmods List of modules that contains patterns. /br See // // # /nsp patterns /href Example /a /br ○ /strong cleanexports Remove exports for exports in module or if Export is from another module add comment to indicate where it comes from./br ○ /strong moveexports Move all exports to just after use clauses./p The /keyword transform command treats the function genEnum as magic and will generate code in a module for enumeration types instead of creating the code by hand. // // # /nsp enum /href genEnum Example /a}"),
helpinfo("unusedsymbols"sub 1,"tools"sub 1,":T(input:seq.file, all:boolean, generated:boolean, excessExports:boolean, ignore:seq.word)seq.word{COMMAND /strong unusedsymbols cmd analyzes code looking for unused functions. /p It forms the function call graph for the program. /br It then looks for any any sources in the call graph that are not the entry point of the program and lists them. Any functions that are generated from type definitions are also removed. /p Here is an example <* block tau tools unusedsymbols /sp+built tools.libsrc taubc.libinfo *> /p The behavior can be modified with flags. /br-/strong all list all unused functions--not just the roots. /br-/strong generated the symbols generated from type definitions are included. /br-/strong excessExports list symbols exported from a module but only used internally to that module./br-/strong ignore Symbols with these names are not listed in output. Default value is genEnum genPEG}"),
helpinfo("usegraph"sub 1,"tools"sub 1,"(input:seq.file, include:seq.word, exclude:seq.word, order:seq.word)seq.word{COMMAND PROFILE /strong usegraph graphs /em use relationship between modules in source code. /br /br options: /br /strong exclude lists the modules to ignore in the use clauses. /br /strong include restricts the modules considered to those listed./br /strong order finds ordering of modules so for any arc in graph the tail occurs befor the head. <* block • /strong nograph Does not include graph in output. *> /p Examples:<* block > usegraph /sp+built core.libsrc // //../documentation/Ex1usegraph.html /href Result /a /br > usegraph /sp+built core.libsrc exclude: seq standard // //../documentation/Ex2usegraph.html /href Result /a /br > usegraph /sp+built core.libsrc include: UTF8 words standard textio exclude: seq standard // //../documentation/Ex3usegraph.html /href Result /a /br > usegraph /sp+core UTF8.ls textio words standard encoding xxhash exclude = seq standard *> /p The last two examples give the same result. The first excludes modules from consideration and the second only includes source files of modules that should be included. }"),
helpinfo("wasm"sub 1,"webassembly"sub 1,"(input:seq.file, Library:seq.word, exports:seq.word, output:seq.word, info:boolean, profile:boolean)seq.file{COMMAND /strong compile to webAssembly}")]

 