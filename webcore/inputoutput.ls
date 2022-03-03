#!/bin/bash  tau -w https://myhost.local/  stdlib   webassembly  wtests wtests  .

module COMPILETIME

use UTF8

use standard

use seq.UTF8

use seq.word

Export+(seq.word, seq.word)seq.word

Export_(seq.word, index)word

Export_(seq.word, int)word

Export_(seq.int, int)int

Export_(seq.char, int)char

Export_(seq.UTF8, int)UTF8

Module inputoutput

use UTF8

use bits

use bitstream

use format

use real

use standard

use tausupport

use textio

use seq.UTF8

use seq.bit

use seq.bits

use process.seq.byte

use seq.byte

use process.seq.int

use bitcast.int

use otherseq.int

use seq.int

use stack.int

use bitcast.intpair

use bitcast.ptr

use seq.real

use bitcast.seq.UTF8

use bitcast.seq.bits

use seq.seq.bits

use bitcast.process.seq.byte

use bitcast.seq.byte

use seq.seq.byte

use bitcast.process.seq.int

use bitcast.seq.int

use seq.seq.int

use bitcast.stack.int

use seq.seq.word

use bitcast.seq.seq.bits

use bitcast.seq.seq.byte

use bitcast.seq.seq.int

type cstr is dummy:seq.bits

Export type:cstr

Function getfile:bit(name:seq.word)seq.bit
assert false report"not implemented"
[tobit.1]

builtin randomfunc real

Function randomint(i:int)seq.int
for acc = empty:seq.int, e ∈ constantseq(i, 0)do acc + intpart.randomfunc /for(acc)

Function stacktrace seq.word"MMMM"

type jsbytes is toreal:real

Export toreal(jsbytes)real

Export type:jsbytes

Function token(s:seq.word)seq.byte toseqbyte.for acc = emptyUTF8, w ∈ s do acc + decodeword.w /for(acc)

Function jsUTF8(t:seq.byte)jsbytes{OPTION NOINLINE}jsbytes.toreal.bitcast:int(toptr.blockIt.t)

Function setElementValue(id:seq.word, text:seq.word)int
{OPTION NOINLINE}intpart.setelementvalue(jsUTF8.token.id, jsUTF8.toseqbyte.HTMLformat.text)

Function setElementValue(id:seq.word, text:jsbytes)int{OPTION NOINLINE}intpart.setelementvalue(jsUTF8.token.id, text)

Builtin bits2real(seq.bits)real

Builtin setelementvalue(name:jsbytes, text:jsbytes)real

Builtin getattributes2(name:jsbytes, text:jsbytes)jsbytes

Function callevent(id:seq.word, event:seq.word)int
{OPTION NOINLINE}intpart.callevent2(jsUTF8.token.id, jsUTF8.token.event)

Builtin callevent2(name:jsbytes, text:jsbytes)real

Builtin setattribute2(name:jsbytes, att:jsbytes, value:jsbytes)real

Builtin getelementvalue(name:jsbytes)jsbytes

Builtin replacesvg(id:jsbytes, xml:jsbytes)real

Function jsmakepair(a:real, h:real)real
let b = bitcast:seq.byte(toptr.intpart.h)
toreal.bitcast:int(toptr.intpair(subseq(b, 1, 1) ≠ toseqbyte.toUTF8."2", "", intpart.h, [intpart.a])
)

type intpair is aborted:boolean, msg:seq.word, msgUTF8:int, body1:seq.int

Function towords(a:jsbytes)seq.word towords.UTF8.bitcast:seq.byte(toptr.intpart.toreal.a)

Function setAttribute(id:seq.word, att:seq.word, value:seq.word)real
setattribute2(jsUTF8.token.id, jsUTF8.token.att, jsUTF8.toseqbyte.HTMLformat.value)

Function getattributes(id:seq.word, attributes:seq.word)seq.word
towords.getattributes2(jsUTF8.token.id, jsUTF8.toseqbyte.HTMLformat.attributes)

Function getElementValue(id:seq.word)seq.word towords.getelementvalue.jsUTF8.token.id

Function getElementValue:jsbytes(id:seq.word)jsbytes getelementvalue.jsUTF8.token.id

Function replaceSVG(name:seq.word, xml0:seq.word)real
let none = "N"_1
let xml = 
 for xml = "", hasquote = none, w ∈ xml0 do
  if w ∈ dq then if hasquote = none then next(xml + w, w)else next(xml + w + space, none)
  else if w ∈ " />"then next(xml + merge(" />" + space), hasquote)
  else next(xml + w, hasquote)
 /for(xml)
replacesvg(jsUTF8.token.name, jsUTF8.toseqbyte.textformat.xml)

Function allocatespace3(i:real)real toreal.bitcast:int(allocatespace.intpart.i)

Function blockseqtype real toreal.blockseqtype:byte

builtin allocatespace(int)ptr

Function set2zero(p:ptr, size:int)ptr if size = 0 then p else set2zero(set(p, 0), size - 1)

Function rootreal(x:real)real sin.x + cos.x + tan.x + sqrt.x + arcsin.x + arccos.x

Builtin jsHTTP(outputbits:real, url:real, method:real, bodydata:real, code:real, pc:real, stk:real, locals:real 
)real

Function HTTP(name:seq.word, method:UTF8, body:seq.byte)process.seq.byte
{OPTION INLINE}
bitcast:process.seq.byte(toptr.intpart.jsHTTP({bits}8.0
, toreal.bitcast:int(toptr.packed.token.name)
, toreal.bitcast:int(toptr.packed.toseqbyte.method)
, toreal.bitcast:int(toptr.packed.body)
, 0.0
, 0.0
, 0.0
, 0.0
)
)

Function HTTP(name:seq.word, method:UTF8, body:seq.int)process.seq.int
{OPTION INLINE}
bitcast:process.seq.int(toptr.intpart.jsHTTP({bits}64.0
, toreal.bitcast:int(toptr.packed.token.name)
, toreal.bitcast:int(toptr.packed.toseqbyte.method)
, toreal.bitcast:int(toptr.packed.body)
, 0.0
, 0.0
, 0.0
, 0.0
)
)

Function getfile:byte(name:seq.word)seq.byte
{OPTION INLINE}
let t = HTTP("/" + name, toUTF8."GET", empty:seq.byte)
if aborted.t then empty:seq.byte else result.t

Function getfile:int(name:seq.word)seq.int
{OPTION INLINE}
let t = HTTP("/" + name, toUTF8."GET", empty:seq.int)
if aborted.t then empty:seq.int else result.t

Function createfile(name:seq.word, data:seq.byte)int
{OPTION INLINE}
let t = 
 HTTP("../cgi-bin/putfile.cgi?" + name
 , toUTF8."PUT Content-Type:application/text"
 , packed.data
 )
if aborted.t then 0 else 1

Function createfile(name:seq.word, data:seq.int)int
{OPTION INLINE}
let t = 
 HTTP("../cgi-bin/putfile.cgi?" + name
 , toUTF8."PUT Content-Type:application/text"
 , packed.data
 )
if aborted.t then 0 else 1

Export undertop(s:stack.int, i:int)int

Export push(s:stack.int, i:int)stack.int

Function poppush(s:stack.int, i:int, val:int)stack.int push(pop(s, i), val)

Builtin stackcall(stk:stack.int, tableidx:int)stack.int

Builtin stackcall2(stk:stack.int, tableidx:int, typoffunc:int)stack.int

Builtin loadvalue(address:int)int

Function resume(r:real, rcode:real, rpc:real, rstk:real, rlocals:real, nopara:real)real
{let z=setElementValue("pageready", "resumeX"+print.bits.intpart.r)}
let code = bitcast:seq.int(toptr.intpart.rcode)
let stk = bitcast:stack.int(toptr.intpart.rstk)
let locals = bitcast:seq.int(toptr.intpart.rlocals)
let x = push(pop(stk, intpart.nopara), representation.r)
let a = interpert(code, intpart.rpc, x, locals)
0.0

Function interpert(code:seq.int, pc:int, stk:stack.int, locals:seq.int)stack.int
let inst = code_pc
let op = tobyte.toint(tobits.inst ∧ 0xFF)
let arg = inst / 256
{let i=setElementValue("pageready", "interpreter"+toword.pc+print.op+toword.arg+for txt="", e /in toseq.stk 
do txt+print.bits.e+"//"/for(txt))}
if pc = 1 then interpert(code, pc + 1, stk, constantseq(arg, 0))
else if op = i64truncf64s then interpert(code, pc + 1, push(pop.stk, intpart.casttoreal.top.stk), locals)
else if op = return then stk
else if op = i32wrapi64 then interpert(code, pc + 1, stk, locals)
else if op = i64mul then
 let args = top(stk, 2)
 interpert(code, pc + 1, push(pop(stk, 2), args_1 * args_2), locals)
else if op = i64add then
 let args = top(stk, 2)
 interpert(code, pc + 1, push(pop(stk, 2), args_1 + args_2), locals)
else if op = i64sub then
 let args = top(stk, 2)
 interpert(code, pc + 1, push(pop(stk, 2), args_1 - args_2), locals)
else if op = i64eq then
 let args = top(stk, 2)
 interpert(code
 , pc + 1
 , push(pop(stk, 2), if args_1 = args_2 then 1 else 0)
 , locals
 )
else if op = i64gts then
 let args = top(stk, 2)
 interpert(code
 , pc + 1
 , push(pop(stk, 2), if args_1 > args_2 then 1 else 0)
 , locals
 )
else if op = f64converti64s then
 interpert(code, pc + 1, push(pop.stk, representation.toreal.top.stk), locals)
else if op ∈ [i64const, i32const]then interpert(code, pc + 1, push(stk, arg), locals)
else if op = f64const then
 let val = representation(toreal.arg / 1000.0)
 interpert(code, pc + 1, push(stk, val), locals)
else if op = localset then interpert(code, pc + 1, pop.stk, replace(locals, arg + 1, top.stk))
else if op = localget then interpert(code, pc + 1, push(stk, locals_(arg + 1)), locals)
else if op = call then
 {callindirect}interpert(code, pc + 2, stackcall2(stk, arg, code_(pc + 1) / 256), locals)
else if op = tobyte.254 then
 {callidx}
 let zz = stackcall2(stk, loadvalue.undertop(stk, 1), arg)
 interpert(code, pc + 1, zz, locals)
else if op = tobyte.255 then
 {this is a call to jsHTML. Control is passed back to javascript and interpreter is resumed after call is compelete.}
 let adjustedstack = 
  push(push(push(push(pop(stk, 4), representation.toreal.bitcast:int(toptr.code))
  , representation.toreal(pc + 2)
  )
  , representation.toreal.bitcast:int(toptr.stk)
  )
  , representation.toreal.bitcast:int(toptr.locals)
  )
 {does not return from following call}stackcall2(adjustedstack, arg, code_(pc + 1) / 256)
else if op = i64load then interpert(code, pc + 1, push(pop.stk, loadvalue(top.stk + arg)), locals)
else if op = br then interpert(code, arg, stk, locals)
else if op = brif then
 interpert(code, if top.stk = 0 then pc + 1 else arg, pop.stk, locals)
else
 let discard = 
  setElementValue("pageready", "not handle by interpreter" + print.op + toword.arg)
 stk

function i64truncf64s byte tobyte.0xB0

function br byte tobyte.0x0C

function brif byte tobyte.0x0D

function return byte tobyte.0x0F

function call byte tobyte.0x10

function i32wrapi64 byte tobyte.0xA7

function i64add byte tobyte.0x7C

function i64sub byte tobyte.0x7D

function i64mul byte tobyte.0x7E

function i64divs byte tobyte.0x7F

function i64eq byte tobyte.0x51

function i64ne byte tobyte.0x52

function i64gts byte tobyte.0x55

function f64converti64s byte tobyte.0xB9

function i64const byte tobyte.0x42

function f32const byte tobyte.0x43

function f64const byte tobyte.0x44

function localget byte tobyte.0x20

function localset byte tobyte.0x21

function i32const byte tobyte.0x41

function i64load byte tobyte.0x29

function tobyte(b:bits)byte tobyte.toint.b 