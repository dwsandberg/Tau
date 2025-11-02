Module SpecialExports

This module is contains functions that must be included in exports of the wasm module because the functions are use by template.js.

use JS.HTTPresult

use SpecialImports

use bits

use bitcast.int

use ptr

use real

use standard

use tausupport

use webIOtypes

Builtin handleerror(real) real

Builtin processbody(real, real) real

Builtin reclaimspace real

use UTF8

Function jsmakepair(data:jsbytes, msgUTF8:jsbytes) JS.HTTPresult
toJS.HTTPresult(UTF8.toseqbyte.msgUTF8, toseqbyte.data)

Function allocatespace3(i:real) real
{used by template.js}
toreal.bitcast:int(allocatespace.intpart.i)

Function randomintimp(i:int) seq.int
for acc = empty:seq.int, e ∈ constantseq(i, 0)
do
 acc
  + toint(
  tobits.representation.randomfunc << 16
  ⊻ (tobits.representation.randomfunc
  ⊻ (tobits.representation.randomfunc >> 16 ⊻ tobits.representation.randomfunc >> 32))
 ),
acc

Function blockseqtype real
{used by template.js}
toreal.blockseqtype:byte 
