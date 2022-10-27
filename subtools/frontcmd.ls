Module frontcmd

use baseTypeCheck

use callconfig

use compilerfrontT.callconfig

use file

use graphcode

use standard

use set.arc.symbol

use graph.symbol

use set.symbol

use symbol2

use set.symdef

Function front(input:seq.file, o:seq.word, pass:seq.word, n:seq.word, ~n:seq.word
, mods:seq.word, ~mods:seq.word, within:boolean, out:seq.word) seq.file
let names = n
let cf = compilerFront:callconfig(if isempty.pass then "pass2" else pass, input)
let prg = prg.cf
let ignorenames = isempty.names ∨ out ∈ ["calls", "calledby"]
for selected = empty:seq.symdef, root = empty:seq.symbol, sd ∈ toseq.prg do
 let ss = sym.sd
 if (isempty.mods ∧ not.isconstantorspecial.ss ∨ name.module.ss ∈ mods)
 ∧ (ignorenames ∨ name.ss ∈ names)
 ∧ name.ss ∉ ~n
 ∧ name.module.ss ∉ ~mods then
  next(selected + sd, if name.ss ∈ names then root + ss else root)
 else next(selected, root)
/for (
 let output = 
  if out = "sym" then
   for txt = "", i ∈ selected do txt + "/p" + %.sym.i /for (txt)
  else if out = "symdef" then
   for txt = "", sd1 ∈ selected do txt + "/p" + %.sym.sd1 + %.code.sd1 /for (txt)
  else if out = "symdefgraph" then
   for txt = "", sd1 ∈ selected do txt + "/p" + %.sym.sd1 + {print} tograph.code.sd1 /for (txt)
  else if out = "baseTypeCheck" then baseTypeCheck(toseq.prg, typedict.cf)
  else if out = "resultCheck" then checkresults.toseq.prg
  else
   let syms = for acc = empty:set.symbol, sd5 ∈ selected do acc + sym.sd5 /for (acc)
   let g = 
    for acc = empty:seq.arc.symbol, sd1 ∈ selected do
     for acc2 = acc, h ∈ toseq(asset.code.sd1 ∩ syms) do
      if sym.sd1 = h ∨ not.within ∧ module.sym.sd1 = module.h then acc2
      else acc2 + arc(sym.sd1, h)
     /for (acc2)
    /for (newgraph.acc)
   let g2 = 
    if out ∈ ["calls", "calledby"] then
     assert not.isempty(nodes.g ∩ asset.root)
     report "no intersection between symbols in option n and call graph"
     subgraph(g, reachable(if out = "calledby" then complement.g else g, root))
    else g
   if out = "text" then
    for txt = "txt", a ∈ toseq.arcs.g do txt + "/br" + %.tail.a + %.head.a /for (txt)
   else drawgraph.newgraph.toseq.arcs.g2
 [file(o, output)])

* The /keyword front command is a multiple purpose command. It outputs data from various stages of
the compiler.

* One use is to figure out what functions are used between modules. The usegraph of the core functions
indicates there are dependences between the modules texio, file and bits.To see the dependences use <*
block front+built stdlib.libsrc mods = textio file bits format *> A graph will be display with the
dependences between the modules. The nodes in the graph are the procedure names. Since a name does
not uniquely identify a function hovering over the beginning of the name will pop up a more complete
discription beginning with the name of the function. 

* The dependence on the module bits will not be displayed. If an earilier pass of the compiler is specified
like this <* block front  +built stdlib.libsrc mods = textio file bits format pass = text *> then
it will be displayed. 

* The dependence with in the module textio can be seen with <* block front  +built stdlib.libsrc mods
= textio pass = text flags = within *>

* To see all the functions that call functions named /em breakparagraph in the library use <* block
front  +built stdlib.libsrc n = breakparagraph pass = text out = calledby *>

* This will list the function definitions in a package <* block front  +built stdlib.libsrc mods =
textio out = symdef *> The format is the function followed by a post order transversal of the call tree
. 

* The front command takes several parameters that control which functions are considered.
/br ○ /strong n = a list of names of functions to include
/br ○ /strong ~n = a list of names to exclude
/br ○ /strong mod = a list of modules to include
/br ○ /strong ~mod = a list of modules to exculde
/br ○ /strong pass = The option pass determines how much processing is done before looking at the symbols
. <* block • /strong library Only report on functions imported from libraries.
/br • /strong text Parse the input in such a way that the source code can be reconstructed.
/br • /strong pass1 Output from first stage of processing. All bindings of text to symbols have been
done.
/br • /strong pass1a Like pass1 with Compiler options on Export statements added. 
/br • /strong pass2 After some optimization
/br • /strong all Just before code generation. *>
/br ○ outThe option out determines what will be output. <* block • sym Just the symbol names
/br • symdefs The symbol definitions. The format is the symbol followed by a post order transversal
of the call tree.
/br • symdefsgraph The symbol definitions a graph of the call tree is provided.
/br • calledby The option n is ignored in building a call graph. Then only the symbols that • call
symbols in n directly or indirectly are included in the graph
/br • calls The option n is ignored in building a call graph. Then only the symbols that • are called
(directly or indirectly) from symbols in n are included in the graph.
/br • txt Instead of production a SVG graph print the args of the graph.
/br • baseTypeCheck
/br • resultCheck *> 