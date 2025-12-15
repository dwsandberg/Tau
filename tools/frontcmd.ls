Module frontcmd.T

precedence > for >1 >2 >3 >4 >alpha

use baseTypeCheck

use file

use seq.file

use graphcode

use prettycompilerfront

use standard

use arc.symbol

use drawGraph.arc.symbol

use graph.arc.symbol

use set.arc.symbol

use set.symbol

use symbol1

use set.symdef

use drawGraph.arc.symloc

unbound compilerFront:T(seq.word, seq.file, seq.word, seq.word) midpoint

Function front:T(
input:seq.file
, output:seq.word
, pass:seq.word
, n:seq.word
, ~n:seq.word
, mods:seq.word
, ~mods:seq.word
, within:boolean
, %:seq.word
) seq.file
{COMMAND The front /strong is a multiple-purpose command. It outputs data from various stages of the compiler. /p
One use is to determine which functions are used between modules. The usegraph of the core functions indicates there are dependencies between the modules texio, file and bits. To see the dependences, use // block front /sp+built core.libsrc mods: textio file bits format /block A graph will be displayed with the dependencies between the modules. The nodes in the graph are the procedure names. Since a name does not uniquely identify a function, hovering over the beginning of the name will pop up a more complete description beginning with the name of the function. /p
The dependence on the module bits will not be displayed. If an earlier pass of the compiler is specified like this // front  +built taubc.libsrc mods = textio file bits format pass = text /block then it will be displayed. /p
The dependence within the module textio can be seen with // front  +built taubc.libsrc mods = textio pass = text within = /block /p
To see all the functions that call functions named /em breakparagraph in the library use // front  +built taubc.libsrc n = breakparagraph pass = text out = calledby /block /p
This will list the function definitions in a package // front  +built taubc.libsrc mods = textio out = symdef /block The format is the function followed by a post order transversal of the call tree. /p
The front command takes several parameters that control which functions are considered./br
○ /strong n a list of names of functions to include /br
○ /strong ~n a list of names to exclude /br
○ /strong mods a list of modules to include /br
○ /strong ~mods a list of modules to exculde /br
○ /strong pass The option pass determines how much processing is done before looking at the symbols. // • /strong library Only report on functions imported from libraries. /br
• /strong text Parse the input in such a way that the source code can be reconstructed./br
• /strong pass1 Output from first stage of processing. All bindings of text to symbols have been done./br
• /strong pass1a Like pass1 with Compiler options on Export statements added. /br
• /strong pass2 After some optimization /br
• /strong all Just before code generation. /block /br
○ /strong % The option % determines the format of the output. // • /strong sym Just the symbol names /br
• /strong symdef The symbol definitions. The format is the symbol followed by a post order transversal of the call tree./br
• /strong symdefgraph For each symbol definition, the definition is presented as a call tree graph./br
• /strong calledby The option n is ignored in building a call graph. Then only the symbols that • call symbols in n directly or indirectly are included in the graph /br
• /strong calls The option n is ignored in building a call graph. Then only the symbols that • are called(directly or indirectly)from symbols in n are included in the graph./br
• /strong txt Instead of producing a SVG graph print the args of the graph./br
• /strong baseTypeCheck /br
• /strong resultCheck /block}
let cf = compilerFront:T(if isempty.pass then "pass2" else pass, input, "*", "")
let out = %
let names = n
let prg = prg.cf
let ignorenames = isempty.names ∨ out ∈ ["calls", "calledby"]
for selected = empty:seq.symdef, root = empty:seq.symbol, sd ∈ toseq.prg
do
 let ss = sym.sd,
 if isconstantorspecial.ss then next(selected, root)
 else if isempty.mods
 ∨ name.module.ss ∈ mods
 ∧ (ignorenames ∨ name.ss ∈ names)
 ∧ name.ss ∉ ~n
 ∧ name.module.ss ∉ ~mods then next(selected + sd, if name.ss ∈ names then root + ss else root)
 else next(selected, root)
let txt =
 if out = "sym" then
  for txt = "", i ∈ selected do txt + "/p" + %.sym.i,
  txt
 else if out = "symdef" then
  for txt = "", sd1 ∈ selected
  do
   let kk = options.sd1,
   txt
   + "/p"
   + %.sym.sd1
   + (if kk = NOOPTIONS then "" else "OPTIONS::(kk)")
   + %.code.sd1,
  txt
 else if out = "symdefgraph" then
  for txt = "", sd1 ∈ selected do txt + "/p" + %.sym.sd1 + drawgraph.tograph.code.sd1,
  txt
 else if out = "baseTypeCheck" then baseTypeCheck(toseq.prg, typedict.cf)
 else if out = "resultCheck" then checkresults.toseq.prg
 else
  let syms =
   for acc = empty:set.symbol, sd5 ∈ selected do acc + sym.sd5,
   acc
  let g =
   for acc = empty:seq.arc.symbol, sd1 ∈ selected
   do
    for acc2 = acc, h ∈ toseq(asset.code.sd1 ∩ syms)
    do
     if sym.sd1 = h ∨ not.within ∧ module.sym.sd1 = module.h then acc2
     else acc2 + arc(sym.sd1, h),
    acc2,
   newgraph.acc,
  let g2 =
   if out ∈ ["calls", "calledby"] then
    assert not.isempty(nodes.g ∩ asset.root) report "no intersection between symbols in option n and call graph",
    subgraph(g, reachable(if out = "calledby" then complement.g else g, root))
   else g,
  if out = "text" then
   for txt = "txt", a ∈ toseq.arcs.g do txt + "/br" + %.tail.a + %.head.a,
   txt
  else drawgraph.newgraph.toseq.arcs.g2,
[file(output, txt)]

Function transform:T(
input:seq.file
, link:seq.file
, output:seq.word
, target:seq.word
, modrename:seq.word
, bind:boolean
, reorguse:boolean
, html:seq.word
, cleanexports:boolean
, moveexports:boolean
, patternmods:seq.word
) seq.file
{COMMAND The transform /strong cmd takes a list of input source files. For each module in the input, a pretty printed file is created in the directory <Tau>/tmp. Additional parameters allow for different variants. // transform+tests profileExample.ls helloworld.ls /br
transform+tests profileExample.ls reorguse:/br
transform  +built profileExample.libsrc	 taubc.libinfo bind:/br
transform  +built profileExample.libsrc	 taubc.libinfo bind: reorguse: /block /p
This first variant does not require the source to be semantically correct, but the syntax must be correct. It does not change the order of the paragraphs. /p
The second is like the first except that it moves the use paragraphs to the beginning of the module, removes duplicates, and sorts them./p
The third is like the first but requires correct semantics. This allows some additional transformations such as // not(a = b)/em to become // a ≠ b /em. /br
○ target /strong overides default target directory tmp /br
○ bind /strong Does further processing of input to bind id's to symbols./br
○ reorguse /strong Reorganizes use clauses. If bind /em is also specified, unnecessary use clauses are removed./br
○ link /strong A list of file names ending with /sp.html that will not be compiled but will be scanned for functions that are called by the files. Hyperlinks will be create from the location of the call to the definition in the link files. Files without a.html extenstion are ignored. /br
○ html /strong An html file is produced with an index of modules. This option is useful for examining source code and contains for producing documentation with imbedded Tau code.This options contains one or more of the following. // • Module /strong Include modules in the table of contents. /br
• headersOnly /strong Only include the headers of exported functions in result./br
• h1 /strong include html h1 headers in table of contents /br
• h2 /strong include html h2 headers in table of contents /br
• h3 /strong include html h3 headers in table of contents /br
• h4 /strong include html h4 headers in table of contents /br
• h5 /strong include html h5 headers in table of contents /br
• h6 /strong include html h6 headers in table of contents /block /br
○ modrename /strong List of modules to rename in form: oldname1 newname1 oldname2 newname2... /br
○ patternmods /strong List of modules that contains patterns. /br
See // // # /nsp patterns /href Example /a /br
○ cleanexports /strong Remove exports for exports in module or if Export is from another module add comment to indicate where it comes from./br
○ moveexports /strong Move all exports to just after use clauses./p
The transform /keyword command treats the function genEnum as magic and will generate code in a module for enumeration types instead of creating the code by hand. // // # /nsp enum /href genEnum Example /a}
let bind1 = bind ∨ not.isempty.link ∨ cleanexports ∨ moveexports
let m = if bind1 then compilerFront:T("text", input, "", "") else empty:midpoint,
transform2(
 m
 , output
 , target
 , modrename
 , bind1
 , reorguse
 , if isempty.link then html else html + "html"
 , cleanexports
 , moveexports
 , input
 , link
 , patternmods
)

Function unusedsymbols:T(
input:seq.file
, all:boolean
, generated:boolean
, excessExports:boolean
, ignore:seq.word
) seq.word
{COMMAND unusedsymbols /strong cmd analyzes code looking for unused functions. /p
It forms the function call graph for the program. /br
It then looks for any sources in the call graph that are not the entry point of the program and lists them. Any functions that are generated from type definitions are also removed. /p
Here is an example tau // tools unusedsymbols /sp+built tools.libsrc taubc.libinfo /block /p
The behavior can be modified with flags. /br
-all /strong list all unused functions--not just the roots. /br
-generated /strong The symbols generated from type definitions are included. /br
-excessExports /strong list symbols exported from a module but only used internally to that module./br
-ignore /strong Symbols with these names are not listed in the output. Default value is genEnum genPEG}
unusedsymbols2(compilerFront:T("text", input, "", ""), all, generated, excessExports, ignore) 