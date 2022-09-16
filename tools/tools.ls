Module tools

* STATE builtin:profile profileinfo profileresult

* usegraph exclude standard seq set otherseq UTF8 real graph file

use doc

use file

use frontcmd

use main2

use profile

use standard

Function front(input:seq.file, o:seq.word, pass:seq.word, n:seq.word, ~n:seq.word
, mods:seq.word, ~mods:seq.word, within:boolean, rn:seq.word, out:seq.word
)seq.file
let output = 
 front2(compilerFront(if isempty.pass then"pass2"else pass, input)
 , n
 , ~n
 , mods
 , ~mods
 , within
 , rn
 , out
 )
[file(o, output)]

* The  /keyword front command is a multiple purpose command. It outputs data from various stages of the compiler.

* One use is to figure out what functions are used between modules. The usegraph of the core functions indicates there
 are dependences between the modules texio, file and bits.To see the dependences use
 /< block front+built stdlib.libsrc mods=textio file bits format  /> A graph will be display with the dependences
 between the modules. The nodes in the graph are the procedure names. Since a name does not uniquely identify a
 function hovering over the beginning of the name will pop up a more complete discription beginning with the name of the
 function. 

* The dependence on the module bits will not be displayed. If an earilier pass of the compiler is specified like this
 /< block front  +built stdlib.libsrc mods=textio file bits format pass=text  /> then it will be displayed. 

* The dependence with in the module textio can be seen with
 /< block front  +built stdlib.libsrc mods=textio pass=text flags=within  />

* To see all the functions that call functions named  /em breakparagraph in the library use
 /< block front  +built stdlib.libsrc n=breakparagraph pass=text out=calledby  />

* This will list the function definitions in a package
 /< block front  +built stdlib.libsrc mods=textio out=symdef  /> The format is the function followed by a post order
 transversal of the call tree. 

* The front command takes several parameters that control which functions are considered.
 /br ○  /strong n=a list of names of functions to include
 /br ○  /strong ~n=a list of names to exclude
 /br ○  /strong mod=a list of modules to include
 /br ○  /strong ~mod=a list of modules to exculde
 /br ○  /strong pass=The option pass determines how much processing is done before looking at the symbols.
 /< block •  /strong library Only report on functions imported from libraries.
 /br •  /strong text Parse the input in such a way that the source code can be reconstructed.
 /br •  /strong pass1 Output from first stage of processing. All bindings of text to symbols have been done.
 /br •  /strong pass1a Like pass1 with Compiler options on Export statements added. 
 /br •  /strong pass2 After some optimization
 /br •  /strong all Just before code generation.  />
 /br ○ outThe option out determines what will be output.
 /< block • sym Just the symbol names
 /br • symdefs The symbol definitions. The format is the symbol followed by a post order transversal of the call tree.
 /br • symdefsgraph The symbol definitions a graph of the call tree is provided.
 /br • calledby The option n is ignored in building a call graph. Then only the symbols that • call symbols in n directly or
 indirectly are included in the graph
 /br • calls The option n is ignored in building a call graph. Then only the symbols that • are called(directly or
 indirectly)from symbols in n are included in the graph.
 /br • txt Instead of production a SVG graph print the args of the graph.
 /br • baseTypeCheck
 /br • resultCheck  />

Function testprofile(input:seq.file, o:seq.word)seq.file
let discard = makebitcode.input
[file(o, profileresults."time")]

Function testprofile2(input:seq.file, o:seq.word)seq.file
let discard = doclibrary(input, o, "")
[file(o, profileresults."time")] 