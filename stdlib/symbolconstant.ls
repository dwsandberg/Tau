Module symbolconstant

use standard

use symbol

use seq.mytype

use seq.symbol

use encoding.symbolconstant

use set.symdef




Function seqelements(s:symbol)seq.symbol
if iswords.s then for acc=empty:seq.symbol , w /in worddata.s  do acc+Word.w /for(acc)
else 
assert isrecordconstant.s report"constant code error" + print.s  
let code1 = fullconstantcode.s
assert isSequence.last.code1 report "constant code error 21" + print.code1  
 code1 >> 1 

Function fullconstantcode(s:symbol)seq.symbol
toseq.decode.to:encoding.symbolconstant(toint.name.s)

Function Constant2( args:seq.symbol)symbol
   symconst(addorder.symbolconstant.args,hasfref.args)
 
function hasfref(args:seq.symbol) boolean  for hasfref =false ,   sym /in args while not.hasfref do 
    hasfref.sym   
  /for( hasfref)


Function hash(s:seq.symbol)int
hash.for acc = "", e ∈ s do acc + worddata.e + name.module.e /for(acc)

function assignencoding(a:symbolconstant)int nextencoding.a

Export type:symbolconstant

type symbolconstant is toseq:seq.symbol

function =(a:symbolconstant, b:symbolconstant)boolean toseq.a = toseq.b

function hash(a:symbolconstant)int hash.toseq.a

Function constantsymbols set.symdef
for acc = empty:set.symdef, i=1,p ∈ encodingdata:symbolconstant do 
next(acc + symdef(symconst(i,hasfref.toseq.p), toseq.p),i+1)/for(acc) 


use sparseseq.symbol

 function map(map0:seq.symbol,prg:seq.symdef) seq.symbol
  for  map=map0, todo=empty:seq.symdef , sd /in prg do
     if isrecordconstant.sym.sd then
      let i=toint.name.sym.sd
      let newmap=for  acc=empty:seq.symbol, ok=true,  sym /in code.sd while ok do
          if isrecordconstant.sym then 
             let mapvalue=map_toint.name.sym
              next(acc+mapvalue,isrecordconstant.mapvalue)
          else 
         next(acc+sym ,ok)
      /for( if ok then replaceS(map, i, [Constant2(acc)]) else  empty:seq.symbol)
     if isempty.newmap then 
       next(map,todo+sd)
    else next(newmap,todo)
    else next(map,todo)
  /for( if isempty.todo then map else 
    assert length.todo < length.prg  report 
"ill formed program"
     +for txt="",sd2 /in todo do txt+"/p"+print.sym.sd2+print.code.sd2 
     /for(txt)
    map(map,todo)
  )
  

use seq.symdef

Function renumberconstants(prg:seq.symdef) seq.symdef
let map=map(sparseseq.Lit.0,prg)
for  newprg=empty:seq.symdef,  sd /in prg do
   if isrecordconstant.sym.sd then newprg else
   let newcode= for acc=empty:seq.symbol,changed=false,sym /in code.sd do
     if isrecordconstant.sym then 
             next( acc+map_toint.name.sym ,true)
     else next(acc+sym,changed)
     /for(if changed then acc else code.sd)
       newprg+symdef(sym.sd,newcode, paragraphno.sd )
    /for( newprg)