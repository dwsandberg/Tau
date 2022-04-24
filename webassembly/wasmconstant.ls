Module wasmconstant

use standard

use symbol2

use seq.mytype

use seq.symbol

use seq.symdef

use set.symdef

use encoding.wasmconstant

use seq.wasmconstant

Function constantcode(s:symbol)seq.symbol
let code1 = fullconstantcode.s
if isSequence.last.code1 then[Lit.0, Lit.nopara.last.code1] + code1 >> 1 else code1 >> 1

function fullconstantcode(s:symbol) seq.symbol
 assert isrecordconstant.s report"constant code error" + print.s
     toseq.(encodingdata:wasmconstant)_toint.name.s 

function Constant2(args:seq.symbol, value:int)symbol 
symconst.addorder.wasmconstant(args)

Function Constant2(args:seq.symbol) symbol
 symconst.addorder.wasmconstant(args)
 
         

Function hash(s:seq.symbol)int
hash.for acc = "", e ∈ s do acc + worddata.e + name.module.e /for(acc)

function assignencoding(a:wasmconstant)int nextencoding.a

Export type:wasmconstant

type wasmconstant is toseq:seq.symbol

function =(a:wasmconstant, b:wasmconstant)boolean toseq.a = toseq.b

function hash(a:wasmconstant)int hash.toseq.a

use sparseseq.seq.symbol

Function oldconstants(prg:set.symdef)int
  for  x=sparseseq.empty:seq.symbol,  sd /in toseq.prg do
     if isrecordconstant.sym.sd then
    replaceS(x,toint.name.sym.sd,[code.sd])
    else x
  /for( for i=1,   e /in x do 
      let discard= if isempty.e then 
        Constant2([Lit.i,Exit],0)
       else Constant2(e,i)
       i+1
       /for(0))
          
