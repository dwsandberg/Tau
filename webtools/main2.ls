

module main2 

use standard

use compileTimeT.wasm

use compilerfrontT.wasm

use file

use seq.file

use symbol2

use textio

use objectio.midpoint

use seq.midpoint

use set.symdef

use seq.modExports

use seq.seq.word

use test11a



Export type:wasm

Function libname(info:midpoint)word extractValue(first.src.info, "Library")_1


Function makebitcode(a:seq.file) seq.file 
assert false report "not implemented"
a

function callfunc:wasm(ctsym:symbol, typedict:typedict, stk:seq.int)seq.int empty:seq.int


Function compilerFront(option:seq.word, input:seq.file)midpoint
{OPTION PROFILE}
let allsrc = breakparagraph.data.input_1
let dep = 
 for mp = empty:midpoint, i ∈ input << 1 do
  let new = first.inbytes:midpoint(data.i)
  midpoint("", prg.mp ∪ prg.new, emptytypedict, libmods.mp + libmods.new, empty:seq.seq.word)
 /for(mp)
compilerfront2:wasm(option, allsrc, dep)

type wasm is a:int

