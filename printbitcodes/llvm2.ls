Module llvm2

use bitcodesupport

use bits

use seq.bits

use seq.block

use seq.byte

use seq.seq.int

use llvm

use standard

type block is bits:SBIT, start:int, len:int, abbrevlen:int, blockid:int

Export type:block

Export abbrevlen(block) int

Export len(block) int

Export bits(block) SBIT

Export start(block) int

Export block(SBIT, int, int, int, int) block

Export blockid(block) int

function sbitindex(a:SBIT, i:int) int
toint(tobits.toint.(sbit.a) sub ((i - 1) / 8 + 1) >> ((i - 1) mod 8) ∧ 0x1)

type SBIT is sbit:seq.byte

type pp is idx:int, val:int

type content is recs:seq.seq.int, blocks:seq.block

Export type:content

Export recs(content) seq.seq.int

Export blocks(content) seq.block

Export type:pp

Export type:SBIT

Export SBIT(seq.byte) SBIT

Export sbit(SBIT) seq.byte

Export val(pp) int

Export idx(pp) int

Function getfixed(a:SBIT, idx:int, size:int) pp
pp(idx + size, toint.getbits(a, idx, size))

Function getbits(a:SBIT, idx:int, size:int) bits
let bidx = (idx - 1) / 8 + 1
let mask = tobits.-1 << size ⊻ tobits.-1,
(toseqbits.subseq(sbit.a, bidx, bidx + (size + 15) / 8)) sub 1
 >> ((idx - 1) mod 8)
 ∧ mask

Function getvbr(a:SBIT, idx:int, size:int) pp getvbr(a, size, bits.0, 0, idx, 0)

Function getvbr(a:SBIT, size:int, val:bits, nobits:int, idx:int, i:int) pp
let b = sbitindex(a, idx + i),
if i = size - 1 then
 if b = 0 then pp(idx + size, toint.val)
 else getvbr(a, size, val, nobits, idx + size, 0)
else getvbr(a, size, bits.b << nobits ∨ val, nobits + 1, idx, i + 1)

Function align32(p:pp) pp
let m = (idx.p - 1) mod 32,
if m = 0 then p else pp(idx.p + 32 - m, 0)

Function getvbrsigned(a:SBIT, idx:int, size:int) pp
if sbitindex(a, idx) = 0 then getvbr(a, size, bits.0, 0, idx, 1)
else
 let p = getvbr(a, size, bits.0, 0, idx, 1),
 pp(idx.p, -val.p)

function getop(b:SBIT, idx:int, opcount:int, result:seq.int) seq.int
if opcount = 0 then [idx] + result
else
 let opbit = sbitindex(b, idx),
 if opbit = 1 then
  let lit = getvbr(b, idx + 1, 8),
  getop(b, idx.lit, opcount - 1, result + 0 + val.lit)
 else
  let code = getfixed(b, idx + 1, 3),
  if val.code ∈ [ABBROPArray, ABBROPChar6, ABBROPBlob] then getop(b, idx.code, opcount - 1, result + val.code)
  else
   let extradata = getvbr(b, idx.code, 5)
   assert val.code ∈ [ABBROPVBR, ABBROPFixed] report "unknown abbreviation op code" + toword.val.code + toword.idx,
   getop(b, idx.extradata, opcount - 1, result + val.code + val.extradata)

Function getinfoB(a:block) content
getinfo(
 bits.a
 , 0
 , empty:seq.int
 , start.a
 , empty:seq.seq.int
 , empty:seq.block
 , abbrevlen.a
 , blockid.a
 , empty:seq.seq.int
)

Function getinfo(
b:SBIT
, noargs:int
, r:seq.int
, idx:int
, recs:seq.seq.int
, blocks:seq.block
, abbrvlen:int
, blockid:int
, abbrdef:seq.seq.int
) content
{if blockid = toint.CONSTANTS then assert false report"X"+toword.idx+@(seperator."/br
", printrecord.toint.CONSTANTS,"", recs)content(recs, blocks)else}
if n.r > 0 then
 {working on record}
 if noargs = 0 then getinfo(b, 0, empty:seq.int, idx, recs + r, blocks, abbrvlen, blockid, abbrdef)
 else
  let next =
   if blockid = toint.CONSTANTS ∧ r sub 1 = toint.CINTEGER then getvbrsigned(b, idx, 6)
   else getvbr(b, idx, 6),
  getinfo(b, noargs - 1, r + val.next, idx.next, recs, blocks, abbrvlen, blockid, abbrdef)
else
 {assert not(blockid = toint.CONSTANTS)report"KK"+toword.length.orderadded.blockabbre+@(seperator."/br
 ", printabbr,"", abbrdef)}
 let t = {getvbr(b, abbrvlen, bits.0, 0, idx, 0)}getfixed(b, idx, abbrvlen)
 {assert val.t = val.getvbr(b, abbrvlen, bits.0, 0, idx, 0)report"XX"+toword.val.t+toword.abbrvlen+toword.val.getvbr(b, abbrvlen, bits.0, 0, idx, 0)}
 if val.t = 3 then
  {record}
  let inst = getvbr(b, idx.t, 6)
  let args = getvbr(b, idx.inst, 6),
  getinfo(b, val.args, [val.inst], idx.args, recs, blocks, abbrvlen, blockid, abbrdef)
 else if val.t = ENTERSUBBLOCK then
  {block}
  let newblockid = getvbr(b, idx.t, 8)
  let abbrlen = getvbr(b, idx.newblockid, 4)
  let alg = align32.abbrlen
  let len = getvbr(b, idx.alg, 32)
  let finish = idx.len + val.len * 32
  let subblock = block(b, idx.len, val.len, val.abbrlen, val.newblockid),
  {let discard = if blockid.subblock = 0 then processabbr(recs.getinfo.subblock, 1, 0, empty:seq.seq.int)else 0}
  getinfo(
   b
   , 0
   , empty:seq.int
   , finish
   , recs + [-1, val.newblockid, n.blocks + 1, val.abbrlen, val.len, idx.len, finish]
   , blocks + subblock
   , abbrvlen
   , blockid
   , abbrdef
  )
 else if val.t = ENDBLOCK then content(recs, blocks)
 else if val.t = DEFINEABBREV then
  let len = getvbr(b, idx.t, 5)
  let ops = getop(b, idx.len, val.len, empty:seq.int),
  let rec = [-2] + postfix(ops, -1),
  getinfo(
   b
   , 0
   , empty:seq.int
   , ops sub 1
   , recs + rec
   , blocks
   , abbrvlen
   , blockid
   , abbrdef + rec
  )
 else
  let rec = readabbrrecord(abbrdef sub (val.t - 3), 2, empty:seq.int, b, idx.t),
  getinfo(
   b
   , 0
   , empty:seq.int
   , rec sub 1
   , recs + subseq(rec, 2, n.rec)
   , blocks
   , abbrvlen
   , blockid
   , abbrdef
  )

Function postfix(s:seq.int, len:int) seq.int
{negative values of len remove len chars from beginning}
if len > 0 then subseq(s, n.s - len + 1, n.s) else subseq(s, -len + 1, n.s)

function readabbrrecord(def:seq.int, i:int, result:seq.int, b:SBIT, idx:int) seq.int
if i > n.def then [idx] + result
else
 let code = def sub i,
 if code = ABBROPFixed then
  let arg = getfixed(b, idx, def sub (i + 1)),
  readabbrrecord(def, i + 2, result + val.arg, b, idx.arg)
 else if code = 0 then readabbrrecord(def, i + 2, result + def sub (i + 1), b, idx)
 else if code = ABBROPArray ∧ def sub (i + 1) = ABBROPChar6 then
  let len = getvbr(b, idx, 6)
  let rec = readarrayfixed(6, b, idx.len, val.len, empty:seq.int),
  readabbrrecord(def, i + 2, result + subseq(rec, 2, n.rec), b, rec sub 1)
 else if code = ABBROPArray ∧ def sub (i + 1) = ABBROPFixed then
  let len = getvbr(b, idx, 6)
  let rec = readarrayfixed(def sub (i + 2), b, idx.len, val.len, empty:seq.int),
  readabbrrecord(def, i + 3, result + subseq(rec, 2, n.rec), b, rec sub 1)
 else
  assert code = ABBROPVBR report
   "not imp abbr"
   + toword.code
   + toword.def sub (i + 1)
   + "idx"
   + toword.idx
   + printabbr.def
  let arg = getvbr(b, idx, def sub (i + 1)),
  readabbrrecord(def, i + 2, result + val.arg, b, idx.arg)

function readarrayfixed(size:int, b:SBIT, idx:int, len:int, result:seq.int) seq.int
if len = 0 then [idx] + result
else
 let data = getfixed(b, idx, 6),
 readarrayfixed(size, b, idx.data, len - 1, result + val.data)
 
