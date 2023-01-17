Module printfunc

use bits

use seq.byte

use funcidx

use standard

use symbol2

use wasm

use otherseq.word

use stack.word

Function printfunc(f:wfunc) seq.word
let nocheck = false
let a = code.f,
if isempty.a then
 %.sym.f + "funcidx = $(funcidx.f) typidx = $(printtypeidx.typeidx.f)"
else
 let typdesc = printtypeidx.typeidx.f
 let argtypes = subseq(typdesc, 3, length.typdesc - 5)
 let d1 = decodeLEBu(a, 1)
 let d2 = decodeLEBu(a, next.d1),
 for text = "", place = next.d2, e ∈ constantseq(value.d2, 1) do
  let d3 = decodeLEBu(a, place),
  next(text + constantseq(value.d3, (%.wtype.a_(next.d3))_1), next.d3 + 1)
 /do
  "($(text))
   /br $(zzz(nocheck, argtypes >> 2 + text, subseq(a, place, length.a - 1), %.sym.f))
   "

Function printcode(a:seq.byte) seq.word zzz(true, "", a, "")

function zzz(nocheck:boolean, locals:seq.word, a:seq.byte, place:seq.word) seq.word
for text = ""
 , op = tobyte.0
 , result = 0x0
 , shift = 0
 , state = "startop"
 , stk = empty:stack.word
 , blkstk = push(empty:stack.word, "?"_1)
 , lastop = tobyte.0
 , byte ∈ a
do
 if state = "startop" then
  if byte
  ∈ [i32divu, i32wrapi64, i32mul, i32add, i32sub
   , i32gtu, i32eq, i32and, tobyte.5, END
   , return, unreachable, i64truncf64s, i32truncf64s, i32truncf64u
   , f64converti32u, i64gts, i64eq, i64add, i64sub
   , i64mul, i64divs, i64extendi32u, i64les, f64converti64s
   , drop, i64ges, i64extendi32s, i32xor, f64converti32s
   , f64gt, f64ge, f64div, f64mul, f64add
   , f64sub, i64and, i64or, i64xor, i64shru
   , i64shl, i32ne, i64reinterpretf64, f64reinterpreti64, memorygrow]
  then
   let newstack = 
    if nocheck then
     stk
    else if byte ∈ [tobyte.05] then
     if top.blkstk = "void"_1 then
      stk
     else
      assert not.isempty.stk ∧ top.stk = top.blkstk report "type problem else $(toseq.stk)+$(top.blkstk)",
      pop.stk
    else if byte ∈ [return, drop] then
     pop.stk
    else if byte ∈ [END] then
     if lastop = unreachable then
      push(stk, top.blkstk)
     else if top.blkstk = "void"_1 then
      stk
     else
      assert top.blkstk = "void"_1 ∨ not.isempty.stk ∧ top.stk = top.blkstk
      report "type problem end $(toseq.stk) /br $(toseq.blkstk) /br $(text)",
      stk
    else
     newstack(byte, stk, text)
   let newblkstk = if byte ∈ [END] then pop.blkstk else blkstk,
   next(text + decodeop.byte
    , byte
    , result
    , shift
    , if byte = memorygrow then "zerobyte" else state
    , newstack
    , newblkstk
    , byte)
  else if byte ∈ [i32load, i32store, i64store, i64load, f64store, f64load, i64load8u] then
   next(text, byte, result, shift, "alignmentbyte", stk, blkstk, lastop)
  else if byte ∈ [tobyte.04, block, loop] then
   next(text, byte, result, shift, "type", stk, blkstk, lastop)
  else if byte ∈ [f64const] then
   next(text, byte, 0x0, 0, "inf64const", stk, blkstk, lastop)
  else
   assert byte
   ∈ [i32const, i64const, localset, localget, localtee
    , call, callindirect, brif, br, tobyte.255]
   report "OPCODE $(decodeop.byte):$(text + stacktrace)",
   next(text, byte, 0x0, shift, "startLEBarg", stk, blkstk, lastop)
 else if state = "inf64const" then
  if shift = 7 then
   next(text + decodeop.op, op, 0x0, 0, "startop", newstack(op, stk, text), blkstk, op)
  else
   next(text, op, 0x0, shift + 1, state, stk, blkstk, op)
 else if state = "type" then
  let newblkstk = push(blkstk, (%.wtype.byte)_1),
  next(text + decodeop.op + %.wtype.byte, op, 0x0, 0, "startop", stk, newblkstk, op)
 else if state = "alignmentbyte" then
  next(text, op, 0x0, 0, "startLEBarg", stk, blkstk, lastop)
 else if state = "zerobyte" then
  assert byte = tobyte.0 report "expected 0 byte $(stacktrace)",
  next(text, op, 0x0, 0, "startop", stk, blkstk, lastop)
 else
  assert state ∈ ["startLEBarg", "inLEB"] report "state problem $(state)"
  let c = tobits.byte ∧ 0x7F,
  if c = tobits.byte then
   let arg = 
    if state = "startLEBarg" then
     toint.if (tobits.byte ∧ 0x40) = 0x0 ∨ op ∉ [i32const, i64const] then
      tobits.byte
     else
      c ∨ tobits.-1 << 7
    else if op ∈ [i32const, i64const] then
     if (tobits.byte ∧ 0x40) = 0x0 then
      toint(result ∨ c << shift)
     else
      toint(result ∨ c << shift ∨ tobits.-1 << (shift + 7))
    else
     toint(result ∨ c << shift)
   let xx = 
    if op = call then
     funcidx2typedesc.arg
    else if op = callindirect then printtypeidx.arg >> 5 else ""
   let newstk = 
    if nocheck then
     stk
    else if op = localset then
     assert between(arg + 1, 1, length.locals)
     report "??? localset problem /br $(text + decodeop.op)" + toword.arg + xx
     assert top.stk = locals_(arg + 1)
     report "type problem localset" + toword.arg + "locals" + locals + "/br" + text,
     pop.stk
    else if op = call then
     assert top(stk, length.xx - 4) = subseq(xx, 3, length.xx - 2)
     report "types nomatch call stk:$(top(stk, length.xx - 4)) xx $(xx) /br $(text)",
     push(pop(stk, length.xx - 4), last.xx)
    else if op = callindirect then
     assert length.xx > 0 report "call indirect $(printtypeidx.arg)"
     assert top(stk, length.xx - 3) = subseq(xx, 3, length.xx - 2) + "i32"
     report
      "types nomatch $(decodeop.op + top(stk, length.xx - 3)) //
       $(subseq(xx, 3, length.xx - 2)) i32"
     assert last.xx ∈ "i32 i64 f64" report "?? callindirect $(xx) $(printtypeidx.arg)",
     push(pop(stk, length.xx - 3), last.xx)
    else if op ∈ [i32store, i64store, f64store, i64load, i64load8u, i32load, f64load, i32const, i64const] then
     newstack(op, stk, text)
    else if op = localget then
     assert between(arg + 1, 1, length.locals) report "localget problem",
     push(stk, locals_(arg + 1))
    else if op = brif then
     assert top(stk, 1) = "i32" report "XXK" + toword.arg + toseq.stk + "/br" + text,
     pop.stk
    else if op = br then
     let blktype = undertop(blkstk, arg),
     if blktype = "void"_1 then
      stk
     else
      assert blktype = top.stk
      report
       "JK" + blktype + top.stk + decodeop.lastop + toword.arg + "/br" + toseq.blkstk
       + "/br"
       + text
      ,
      pop.stk
    else
     assert op ∈ [localtee] report "OPCODEX $(decodeop.op):$(text) stk $(toseq.stk)"
     assert between(arg + 1, 1, length.locals)
     report "??? localtee problem /br $(text) $(decodeop.op)" + toword.arg + xx
     assert top.stk = locals_(arg + 1)
     report "type problem localtee" + toword.arg + "locals" + locals + "/br" + text,
     stk
   ,
   next(text + decodeop.op + toword.arg + xx
    , op
    , 0x0
    , 0
    , if op = callindirect then "zerobyte" else "startop"
    , newstk
    , blkstk
    , op)
  else if state = "startLEBarg" then
   next(text, op, c, 7, "inLEB", stk, blkstk, lastop)
  else
   let newresult = result ∨ c << shift,
   next(text, op, newresult, shift + 7, state, stk, blkstk, lastop)
/do "P $(text)"

function newstack(op:byte, stk:stack.word, text:seq.word) stack.word
let d = 
 if op ∈ [i64mul, i64sub, i64add, i64divs, i64shl, i64shru, i64or, i64and, i64xor] then
  ["i64 i64", "i64"]
 else if op ∈ [i64gts, i64eq, i64les, i64ges] then
  ["i64 i64", "i32"]
 else if op ∈ [i32wrapi64] then
  ["i64", "i32"]
 else if op ∈ [f64converti32u, f64converti32s, f64load] then
  ["i32", "f64"]
 else if op ∈ [f64converti64s, f64reinterpreti64] then
  ["i64", "f64"]
 else if op ∈ [i64truncf64s, i64reinterpretf64] then
  ["f64", "i64"]
 else if op ∈ [i32truncf64s, i32truncf64u] then
  ["f64", "i32"]
 else if op ∈ [i32mul, i32add, i32sub, i32gtu, i32eq, i32and, i32ne, i32xor, i32or] then
  ["i32 i32", "i32"]
 else if op ∈ [i32store] then
  ["i32 i32", ""]
 else if op ∈ [i64store] then
  ["i32 i64", ""]
 else if op ∈ [f64store] then
  ["i32 f64", ""]
 else if op ∈ [i32load, memorygrow] then
  ["i32", "i32"]
 else if op ∈ [i64load, i64load8u, i64extendi32u, i64extendi32s] then
  ["i32", "i64"]
 else if op ∈ [i64const] then
  ["", "i64"]
 else if op ∈ [i32const] then
  ["", "i32"]
 else if op ∈ [f64const] then
  ["", "f64"]
 else if op ∈ [f64gt, f64ge] then
  ["f64 f64", "i32"]
 else if op ∈ [f64add, f64mul, f64div, f64sub] then
  ["f64 f64", "f64"]
 else if op = unreachable then
  ["", ""]
 else
  assert false report "newstack $(decodeop.op)",
  ["", ""]
assert length.toseq.stk ≥ length.d_1 ∧ top(stk, length.d_1) = d_1
report "type problem $(decodeop.op) stk: $(toseq.stk) /br $(text)",
if isempty.d_2 then pop(stk, length.d_1) else push(pop(stk, length.d_1), d_2_1) 