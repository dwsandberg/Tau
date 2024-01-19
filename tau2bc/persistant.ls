Module persistant

use UTF8

use bits

use seq.byte

use encoding.seq.char

use seq.seq.char

use encoding.const3

use seq.const3

use llvm

use llvmcode

use seq.slot

use standard

use word

use encoding.word3

use seq.encoding.word3

use set.encoding.word3

Export type:word3

type word3 is chars:seq.char

function word3(a:word) word3 word3.decodeword.a

function slotX(a:word3) int toint.C64.valueofencoding.encode.a

function =(a:word3, b:word3) boolean chars.a = chars.b

function hash(a:word3) int hash.chars.a

Function constdata seq.slot
for acc = empty:seq.slot, @e ∈ encodingdata:const3
do acc + flds.@e,
acc

type const3 is place:int, flds:seq.slot

function =(a:const3, b:const3) boolean flds.a = flds.b

function =(a:slot, b:slot) boolean toint.a = toint.b

function hash(a:const3) int
for acc = empty:seq.int, @e ∈ flds.a do acc + toint.@e,
hash.acc

Function wordref(w:word) int
{identity, y}
let w3 = word3.w
let discard = encode.w3,
slotX.w3

Function addint(i:int) int toint.C64.i

Function initwordref(baselibwords:seq.seq.char, bcwords:seq.char) int
for acc = 0, @e ∈ baselibwords
do max(acc, valueofencoding.asencoding.encodeword.@e)
for acc2 = 0, k ∈ subseq(encodingdata:seq.char, 1, acc)
do valueofencoding.encode.word3.k,
loadbcwords.bcwords

Function wordstoadd(baselibwords:seq.seq.char) seq.encoding.word3
let have =
 for acc = empty:set.encoding.word3, @e ∈ baselibwords
 do acc + encode.word3.@e,
 acc
let used =
 for acc = empty:set.encoding.word3, @e ∈ encodingdata:word3
 do acc + encode.@e,
 acc,
toseq(used \ have)

Function commonwords(wordstoadd:seq.encoding.word3) seq.byte
for out = emptyUTF8, w ∈ wordstoadd
do out + chars.decode.w + bcwordsep,
toseqbyte.out

Function bytes(i:int) seq.byte
for acc = empty:seq.byte, shift = 0
while shift < 64
do next(acc + tobyte.toint(tobits.i >> shift ∧ 0xFF), shift + 8),
acc

function loadbcwords(bcwords:seq.char) int
for acc = empty:seq.char, c ∈ bcwords
do
 if c = bcwordsep then
  let discard0 = encodeword.acc
  let discard = encode.word3.acc,
  empty:seq.char
 else acc + c,
0

Function wordreps2(wordstoadd:seq.encoding.word3) int
for acc = [toint.C64.0, toint.C64.n.wordstoadd], w ∈ wordstoadd
do
 let s = tointseq.chars.decode.w
 for acc2 = [toint.C64.0, toint.C64.n.s], ch ∈ s
 do acc2 + toint.C64.ch,
 acc + addobject.acc2,
addobject.acc

Function addobject2(name:seq.word, data:seq.int) int
let objtype = array(n.data, i64)
for acc = empty:seq.slot, @e ∈ data do acc + asi64.slot.@e,
toint.CGEP(slot.global(name, objtype, AGGREGATE.acc), 0)

Function global(name:seq.word, type:llvmtype, init:slot) int
toint.modulerecord(name, [toint.GLOBALVAR, typ.type, 2, 1 + toint.init, 0, toint.align8 + 1, 0])

Function addobject(fldsin:seq.int) int
let flds =
 for acc = empty:seq.slot, @e ∈ fldsin
 do acc + asi64.slot.@e,
 acc
let t = encodingdata:const3
let place = if n.t = 0 then 0 else place.1^t + n.flds.1^t
let x = decode.encode.const3(place, flds)
let idx = if place.x ≠ place then place.x else place,
toint.CGEP(modulerecord("list", [0]), idx)

Function addwordseq(a:seq.word) int
for acc = [toint.C64.0, toint.C64.n.a], @e ∈ a
do acc + wordref.@e,
addobject.acc 