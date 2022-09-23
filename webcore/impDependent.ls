Module impDependent

use UTF8

use bits

use file

use format

use real

use standard

use tausupport

use seq.byte

use seq.file

use bitcast.int

use otherseq.int

use seq.int

use stack.int

use bitcast.processrecord

use bitcast.seq.byte

use process.seq.byte

use seq.seq.byte

use bitcast.seq.int

use process.seq.int

use bitcast.stack.int

use bitcast.process.seq.byte

use bitcast.process.seq.int

use SpecialImports

Function HTTP(name:seq.word, header:seq.word, body:seq.byte, followfunc:seq.word, state:state)real
{OPTION INLINE}
jsHTTP(token.name
, jsUTF8.toseqbyte.toUTF8.header
, jsUTF8.body
, token.followfunc
, toreal.bitcast:int(toptr.state)
)

Function readfiles(files:seq.file, args:seq.word, callback:seq.word)real
let z = 
 decodeZ(jHTTP.0.0, jHTTP2.toreal.bitcast:int(toptr.state(files, args, 0, callback, "GET")))
0.0

Function writefiles(files:seq.file, args:seq.word, callback:seq.word)real
let z = 
 decodeZ(jHTTP.0.0
 , jHTTP2.toreal.bitcast:int(toptr.state(files, args, 0, callback, "PUT Content-Type:application/text"))
 )
0.0

type jHTTP is r:real

Export type:jHTTP

use RI.state

type jHTTP2 is r:real

Export type:jHTTP2

Export r(jHTTP2)real

Export jHTTP2(real)jHTTP2

use otherseq.file

use bitcast:jHTTP2

use bitcast:RI.state

Function decodeZ(h:jHTTP, h2:jHTTP2)state decodeZx(h, bitcast:RI.state(toptr.h2))

Function decodeZx(h:jHTTP, h2:RI.state)state
let s = fromRI.h2
{let k=bitcast:state(toptr.intpart.r.h2)let s=fromRI.toRI.k}
let newfiles = 
 if idx.s > 0 ∧ method.s = "GET" ∧ not.isempty.files.s then
  replace(files.s, idx.s, file(fn.(files.s)_(idx.s), result.bitcast:process.seq.byte(toptr.intpart.r.h)))
 else files.s
let newstate = state(newfiles, args.s, idx.s + 1, finalcall.s, method.s)
if isempty.files.s ∧ idx.s = 0 then
 let t = HTTP("", "NONE", empty:seq.byte, finalcall.s, newstate)
 {never gets here}s
else if idx.s ≥ length.files.s then newstate
else
 let nameprefix = 
  if method.s = "GET"then"/"else"../cgi-bin/putfile.cgi?"
 let this = (files.s)_(idx.newstate)
 let t = 
  HTTP(nameprefix + fullname.fn.this
  , method.s
  , data.this
  , if idx.newstate = length.files.s then finalcall.s else"decodeZ"
  , newstate
  )
 {never gets here}newstate

Export type:jHTTP

use bitcast:state

type state is files:seq.file, args:seq.word, idx:int, finalcall:seq.word, method:seq.word

Export type:state

Export files(state)seq.file

Export args(state)seq.word

type jsbytes is toreal:real

Export toreal(jsbytes)real

Export type:jsbytes

Function token(s:seq.word)jsbytes
jsUTF8.toseqbyte.for acc = emptyUTF8, w ∈ s do acc + decodeword.w /for(acc)

Function jsUTF8(t:seq.byte)jsbytes{OPTION NOINLINE}jsbytes.toreal.bitcast:int(toptr.packed.t)

_________________

Function randomintimp(i:int)seq.int
for acc = empty:seq.int, e ∈ constantseq(i, 0)do
 acc
 + toint.xor(tobits.representation.randomfunc << 16
 , xor(tobits.representation.randomfunc
 , xor(tobits.representation.randomfunc >> 16, tobits.representation.randomfunc >> 32)
 )
 )
/for(acc)

Function getattributes(id:seq.word, attributes:seq.word)seq.word
towords.getattributes2(token.id, jsUTF8.toseqbyte.HTMLformat.attributes)

Function setAttribute(id:seq.word, att:seq.word, value:seq.word)real
setattribute2(token.id, token.att, jsUTF8.toseqbyte.HTMLformat.value)

Function callevent(id:seq.word, event:seq.word)int{OPTION NOINLINE}intpart.callevent2(token.id, token.event)

Function replaceSVG(name:seq.word, xml0:seq.word)real
let none = "N"_1
let xml = 
 for xml = "", hasquote = none, w ∈ xml0 do
  if w ∈ dq then if hasquote = none then next(xml + w, w)else next(xml + w + space, none)
  else if w ∈ " />"then next(xml + merge(" />" + space), hasquote)
  else next(xml + w, hasquote)
 /for(xml)
replacesvg(token.name, jsUTF8.toseqbyte.textformat.xml)

_______________________

Function jsmakepair(data:jsbytes, msgUTF8:jsbytes)real
let b = toseqbyte.msgUTF8
toreal.bitcast:int(toptr.processrecord(subseq(b, 1, 1) ≠ toseqbyte.toUTF8."2", "", b, [toseqbyte.data])
)

type processrecord is aborted:boolean, msg:seq.word, msgUTF8:seq.byte, body1:seq.seq.byte

Function towords(a:jsbytes)seq.word towords.UTF8.toseqbyte.a

function toseqbyte(a:jsbytes)seq.byte bitcast:seq.byte(toptr.intpart.toreal.a)

Function allocatespace3(i:real)real{used by template.js}toreal.bitcast:int(allocatespace.intpart.i)

Function blockseqtype real{used by template.js}toreal.blockseqtype:byte

builtin allocatespace(int)ptr

Function set2zero(p:ptr, size:int)ptr
{used in wasm2.ls}if size = 0 then p else set2zero(set(p, 0), size - 1)

Function rootreal(x:real)real sin.x + cos.x + tan.x + sqrt.x + arcsin.x + arccos.x

Function finishentry(seq.file)UTF8
assert false report"not implemented"
emptyUTF8

Function getfiles(args:seq.word)seq.file
assert false report"not implemented"
empty:seq.file 




Module RI.T


use bitcast.T

use bitcast.real

use bitcast.int

use real

type RI is val:T

Export type:RI.T

Function toRI(a:T) RI.T
 RI.bitcast:T(toptr.toreal.bitcast:int(toptr.a))

Function fromRI(a:RI.T) T
 bitcast:T(toptr.intpart.casttoreal.bitcast:int(toptr.val.a))

let s = bitcast:state(toptr.intpart.r.h2)

