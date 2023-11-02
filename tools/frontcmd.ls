Module frontcmd.T

use baseTypeCheck

use file

use graphcode

use prettycompilerfront

use standard

use set.arc.symbol

use graph.symbol

use set.symbol

use symbol2

use set.symdef

unbound compilerFront:T(seq.word, seq.file) midpoint

Function front:T(
 input:seq.file
 , o:seq.word
 , pass:seq.word
 , n:seq.word
 , ~n:seq.word
 , mods:seq.word
 , ~mods:seq.word
 , within:boolean
 , out:seq.word
) seq.file
{COMMAND The /strong front is a multiple purpose command. It outputs data from various stages of
the compiler. 
/p One use is to figure out what functions are used between modules. The usegraph of the core
functions indicates there are dependences between the modules texio, file and bits. To see the
dependences use <* block front+built stdlib.libsrc mods = textio file bits format *> A graph
will be display with the dependences between the modules. The nodes in the graph are the
procedure names. Since a name does not uniquely identify a function hovering over the beginning
of the name will pop up a more complete discription beginning with the name of the function. 
/p The dependence on the module bits will not be displayed. If an earilier pass of the compiler
is specified like this <* block front  +built stdlib.libsrc mods = textio file bits format pass
= text *> then it will be displayed. 
/p The dependence with in the module textio can be seen with <* block front  +built stdlib.
libsrc mods = textio pass = text within = *>
/p To see all the functions that call functions named /em breakparagraph in the library use <*
block front  +built stdlib.libsrc n = breakparagraph pass = text out = calledby *>
/p This will list the function definitions in a package <* block front  +built stdlib.libsrc
mods = textio out = symdef *> The format is the function followed by a post order transversal of
the call tree. 
/p The front command takes several parameters that control which functions are considered.
/br ○ /strong n a list of names of functions to include
/br ○ /strong ~n a list of names to exclude
/br ○ /strong mods a list of modules to include
/br ○ /strong ~mods a list of modules to exculde
/br ○ /strong pass The option pass determines how much processing is done before looking at the
symbols. <* block • /strong library Only report on functions imported from libraries.
/br • /strong text Parse the input in such a way that the source code can be reconstructed.
/br • /strong pass1 Output from first stage of processing. All bindings of text to symbols have
been done.
/br • /strong pass1a Like pass1 with Compiler options on Export statements added. 
/br • /strong pass2 After some optimization
/br • /strong all Just before code generation. *>
/br ○ /strong out The option out determines what will be output. <* block • /strong sym Just the
symbol names
/br • /strong symdef The symbol definitions. The format is the symbol followed by a post order
transversal of the call tree.
/br • /strong symdefgraph For each symbol definition, the definition is presented as a call tree
graph.
/br • /strong calledby The option n is ignored in building a call graph. Then only the symbols
that • call symbols in n directly or indirectly are included in the graph
/br • /strong calls The option n is ignored in building a call graph. Then only the symbols that
• are called (directly or indirectly) from symbols in n are included in the graph.
/br • /strong txt Instead of producing a SVG graph print the args of the graph.
/br • /strong baseTypeCheck
/br • /strong resultCheck *>}
let cf = compilerFront:T(if isempty.pass then "pass2" else pass, input)
let names = n
let prg = prg.cf
let ignorenames = isempty.names ∨ out ∈ ["calls", "calledby"]
for selected = empty:seq.symdef, root = empty:seq.symbol, sd ∈ toseq.prg
do
 let ss = sym.sd,
  if isconstantorspecial.ss then
  next(selected, root)
  else if
   isempty.mods
    ∨ 
    name.module.ss ∈ mods
     ∧ (ignorenames ∨ name.ss ∈ names)
     ∧ name.ss ∉ ~n
     ∧ name.module.ss ∉ ~mods
  then
  next(selected + sd, if name.ss ∈ names then root + ss else root)
  else next(selected, root)
let output =
 if out = "sym" then
 for txt = "", i ∈ selected do txt + "/p" + %.sym.i, txt
 else if out = "symdef" then
  for txt = "", sd1 ∈ selected
  do
   let kk = getOptions.sd1,
   txt + "/p" + %.sym.sd1 + (if isempty.kk then "" else "OPTIONS:^(kk)") + %.code.sd1,
  txt
 else if out = "symdefgraph" then
 for txt = "", sd1 ∈ selected do txt + "/p" + %.sym.sd1 + {print} tograph.code.sd1, txt
 else if out = "baseTypeCheck" then
 baseTypeCheck(toseq.prg, typedict.cf)
 else if out = "resultCheck" then
 checkresults.toseq.prg
 else
  let syms = for acc = empty:set.symbol, sd5 ∈ selected do acc + sym.sd5, acc
  let g =
   for acc = empty:seq.arc.symbol, sd1 ∈ selected
   do
    for acc2 = acc, h ∈ toseq(asset.code.sd1 ∩ syms)
    do
     if sym.sd1 = h ∨ not.within ∧ module.sym.sd1 = module.h then
     acc2
     else acc2 + arc(sym.sd1, h),
    acc2,
   newgraph.acc
  let g2 =
   if out ∈ ["calls", "calledby"] then
    assert not.isempty(nodes.g ∩ asset.root)
    report "no intersection between symbols in option n and call graph",
    subgraph(g, reachable(if out = "calledby" then complement.g else g, root))
   else g,
   if out = "text" then
   for txt = "txt", a ∈ toseq.arcs.g do txt + "/br" + %.tail.a + %.head.a, txt
   else drawgraph.newgraph.toseq.arcs.g2,
[file(o, output)]

Function transform:T(
 input:seq.file
 , o:seq.word
 , target:seq.word
 , modrename:seq.word
 , bind:boolean
 , reorguse:boolean
 , html:seq.word
 , cleanexports:boolean
 , moveexports:boolean
 , patternmods:seq.word
) seq.file
{COMMAND The /strong transform cmd takes a list of input source files. For each module in the
input a pretty printed file is in the directory <Tau>/tmp Addition parameters allows for different
variants. <* block transform helloworld/helloworld.ls
/br transform helloworld/helloworld.ls reorguse =
/br transform  +built HelloWorld.libsrc	 stdlib.libinfo bind =
/br transform  +built HelloWorld.libsrc	 stdlib.libinfo bind = reorguse = *>
/p This first variant does not require the source to be sematicaly correct but the syntax must be
correct. It does not change the order of the paragraphs. 
/p The second is like the first except that it moves the use paragraphs to the beginning of the
module, removes duplicates, and sorts them.
/p The third is like the first but requires correct semantics. This allows some additional
transformations such as" not (a = b)" to become" a /ne b"
/br ○ /strong target overides default target directory tmp
/br ○ /strong bind Does further processing of input to bind id's to symbols.
/br ○ /strong reorguse Reorganizes use clauses. If /em bind is also specified unnecessary use
clauses are removed.
/br ○ /strong html An html file is produced with an index of modules. This option is useful for
examining source code Useful for producing documentation with imbedded Tau code.
/br ○ /strong modrename List of modules to rename in form: oldname1 newname1 oldname2 newname2.
.. 
/p The /keyword transform command treats the function genEnum as magic and will generate code in a
module for enumeration types instead of creating the code by hand. /tag <a /sp a href ="#enum
" > Example /tag </a>}
let m =
 if bind ∨ cleanexports ∨ moveexports then
 compilerFront:T("text", input)
 else empty:midpoint,
transform2(m, o, target, modrename, bind, reorguse, html, cleanexports, moveexports, input, patternmods)

Function unusedsymbols:T(
 input:seq.file
 , o:seq.word
 , all:boolean
 , generated:boolean
 , excessExports:boolean
 , ignore:seq.word
) seq.file
{COMMAND The /strong unusedsymbols cmd analyzes code for unused functions. It forms the function
call graph for the program. 
/br It then looks for any any sources in the call graph that are not the entry point of the program
and lists them. Any functions that are generated from type definitions are also removed. 
/p Here is an example <* block tau tools unusedsymbols+built tools.libsrc stdlib.libinfo
common *>
/p The behavior can be modified with flags. 
/br • /strong all list all unused functions--not just the roots. 
/br • /strong generated the symbols generated from type definitions are included. 
/br • /strong excessExports list symbols exported from a module but only used internally to that
module.
/br • /strong ignore Symbols with these names are not listed in output. Default value is genEnum
genPEG}
[file(o, unusedsymbols2(compilerFront:T("text", input), all, generated, excessExports, ignore))] 