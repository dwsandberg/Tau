Module seqiohelp

use UTF8

use bits

use format

use packedindex

use real

use standard

use symbol2

use tausupport

use textio

use bitcast.int

use seq.int

use otherseq.mytype

use seq.mytype

use set.mytype

use encoding.outrec

use bitcast.ptr

use seq.ptr

use bitcast.real

use seq.symbol

use bitcast.word

use bitcast.seq.int

use seq.seq.int

use seq.seq.mytype

use seq.encodingpair.outrec

use bitcast.seq.ptr

use seq.seq.word

use bitcast:seq.word

function towordS(i:int)seq.word if i < 0 then"-" + toword.-i else[toword.i]

Function toSeqSeqInt(a:seq.word)seq.seq.int
for acc = empty:seq.seq.int, last = first."^", this ∈ a do
 if last ∈ "^"then
  assert this ∈ "="report"error"
  next(acc + [empty:seq.int], this)
 else if this ∈ "-^"then next(acc, this)
 else
  {this is number}
  if last ∈ "-"then next(acc >> 1 + (last.acc + -toint.this), this)
  else next(acc >> 1 + (last.acc + toint.this), this)
/for(acc)

function print(l:seq.mytype)seq.word for t2 = "", t ∈ l do t2 + print.t /for(t2) + EOL

Function fileformat(a0:seq.seq.mytype)seq.word
let a = [[typeword, typeword], [typeint, typeint], [typereal, typereal]] + a0
let z1 = 
 for single = empty:seq.seq.mytype, row ∈ a do
  if length.row = 2 ∧ not.isseq.last.row ∧ not.isseq.first.row then single + row else single
 /for(if isempty.single then a
 else
  {remove types not represented by a record}
  for result = empty:seq.seq.mytype, old = empty:set.mytype, new = empty:set.mytype, row2 ∈ a do
   let tmp = for acc = [first.row2], t ∈ row2 << 1 do acc + sub(t, single)/for(acc)
   next(result + tmp, old + first.tmp, new ∪ asset(tmp << 1))
  /for(let new1 = 
   for new1 = empty:set.mytype, e ∈ toseq.new do new1 + if isseq.e then parameter.e else e /for(new1)
  for acc = result, e ∈ toseq(new1 \ old)do result + [e, e]/for(acc))/if)
for t2 = "", row ∈ z1 do
 for t3 = "", t ∈ row << 1 do
  t3
  + if isseq.t then
   let p = parameter.t
   for acc = 0, idx = 1, row2 ∈ z1 while acc = 0 do next(if first.row2 = p then-idx else acc, idx + 1)/for([toword.acc])
  else
   let z = findindex(t, [typeword, typeint, typereal])
   assert z < 4 report"???" + print.t
   [toword.z]
 /for(t2 + "=" + t3 + "^")
/for(t2)

function sub(t:mytype, s:seq.seq.mytype)mytype
if t ∈ [typeint, typeword, typereal]then t
else if isseq.t then seqof.sub(parameter.t, s)
else
 for acc = t, row ∈ s do if t = first.row then last.row else acc /for(acc)

function print(z1:seq.seq.mytype)seq.word for t2 = "", t ∈ z1 do t2 + print.t /for(t2)

function print(z:seq.seq.int)seq.word
for t2 = "", e2 ∈ z do
 for t1 = "", e1 ∈ e2 do t1 + toword.e1 + ", "/for(t2 + ", [" + t1 >> 1 + "]" + EOL)
/for(t2 << 1)

function printformat(s:seq.seq.int, sep:seq.word)seq.word
for acc = "=1" + sep + "=2" + sep + "=3" + sep, r ∈ s do
 for line = "=", e ∈ r do
  line + if e < 0 then"-" + toword.-e else[toword.e]
 /for(acc + line + sep)
/for(acc)

type outrec is val:seq.word, ptrval:int

function =(a:outrec, b:outrec)boolean val.a = val.b

function hash(a:outrec)int hash.val.a

function assignencoding(a:outrec)int ptrval.a

type ptr/size is ptrval:int, next:int, size:int, done:UTF8, pending:UTF8

function ptr(a:ptr/size)word toword.ptrval.a

Function outrec3(a:ptr/size, this:seq.word, add:int, saverec:boolean)ptr/size
assert this = towords.toUTF8(this, perserveFormat, true)
report"XX" + this + EOL + towords.toUTF8(this, perserveFormat, true)
let ptrval = if saverec then valueofencoding.encode.outrec(this, next.a)else next.a
if ptrval < next.a then ptr/size(ptrval, next.a, size.a, done.a, pending.a)
else if size.a + add ≥ {2000}2000 then
 ptr/size(ptrval
 , next.a + 1
 , add
 , done.a + toUTF8("size" + toword.size.a, perserveFormat, true) + char.10 + pending.a
 , toUTF8(this, perserveFormat, true) + char.10
 )
else
 ptr/size(ptrval
 , next.a + 1
 , size.a + add
 , done.a
 , pending.a + toUTF8(this, perserveFormat, true) + char.10
 )

Function onerecord(p:ptr, typ:int, pattern:seq.seq.int, sizex:ptr/size)ptr/size
let sizein = size.sizex
if typ < 0 then
 if typ = -2 then
  let seqp = bitcast:seq.int(p)
  assert length.seqp + 2 < 12600 report"problem onerecord" + toword(length.seqp + 2)
  let this = 
   for this = "", ele ∈[-2, 0, length.seqp] + seqp do this + towordS.ele /for(this)
  outrec3(sizex, this, length.seqp + 2, false)
 else
  {sequence}
  let seqp = bitcast:seq.ptr(p)
  let packed = if getseqtype.seqp = 1 then length.pattern_(-typ)else 0
  let blksize = 40
  for this = towordS.typ + ["0, "_1, toword.min(length.seqp, blksize)]
  , size = sizex
  , idx = 0
  , blks = ""
  , i = 1
  , ele ∈ seqp
  do
   let t = 
    onerecord(if packed > 0 then packedindex(p, packed, i)else ele, -typ, pattern, size)
   if idx = blksize then
    let blk = outrec3(t, this, blksize + 2, false)
    let seqlen = min(length.seqp - blksize * (length.blks + 1), blksize)
    next(towordS.typ + ["0"_1, toword.seqlen] + ptr.t, blk, 1, blks + ptr.blk, i + 1)
   else next(this + ptr.t, t, idx + 1, blks, i + 1)
  /for(let seqlen = min(length.seqp - blksize * length.blks, blksize)
  let a = outrec3(size, this, seqlen + 2, length.pattern > 4)
  if isempty.blks then a
  else
   outrec3(a, towordS.typ + [toword.blksize, toword.length.seqp] + blks + ptr.a, length.blks + 3, true)/if)
else if length.pattern_typ = 1 then onerecord(p, pattern_typ_1, pattern, sizex)
else
 for acc = [toword.typ], idx = 0, size = sizex, current ∈ pattern_typ do
  let acc0 = acc
  if current = 1 then
   let t = fld:word(p, idx)
   next(acc0 + fld:word(p, idx), idx + 1, size)
  else if current = 2 then next(acc0 + towordS.fld:int(p, idx), idx + 1, size)
  else if current = 3 then next(acc0 + print(5, fld:real(p, idx)), idx + 1, size)
  else if current = -1 then
   let s = fld:seq.word(p, idx)
   let words = 
    if dq_1 ∉ s then dq + s + dq
    else
     assert"'"_1 ∉ s report"did not find delimiter for sring"
     "'" + s + "'"
   next(acc0 + words, idx + 1, size)
  else
   let p1 = fld:int(p, idx)
   let t = onerecord(fld:ptr(p, idx), current, pattern, size)
   next(acc + ptr.t, idx + 1, t)
 /for(outrec3(size, acc, idx, length.pattern > 4))

Function subwrite(ptr:ptr, a:seq.word, name:seq.word)seq.word
let fileformat = toSeqSeqInt.a
let z = onerecord(ptr, -4, fileformat, ptr/size(0, 1, 0, emptyUTF8, emptyUTF8))
let txt2 = toUTF8.a + char.10 + done.z + toUTF8("size" + toword.size.z) + char.10 + pending.z
let discard2 = createfile(name, toseqbyte.txt2)
"done"

function WORD int 1

function WORDS int-1

function INT int 2

function REAL int 3

function CHANGE int 2000

function PATTERN int 2001

function SIZE int 2003

function STARTREC int 2002

Function subread(datain:seq.word)ptr
let a1 = allocatespace.1
for acc = a1
, stateidx = 1
, statepattern = [STARTREC]
, repeat = 1
, fld = ""
, offsets = empty:seq.ptr
, patterns = empty:seq.seq.int
, w ∈ datain
do
 assert stateidx ≤ length.statepattern report"/??" + toword.stateidx + print.[statepattern]
 let state = statepattern_stateidx
 if state = PATTERN then
  if w ∈ "-"then next(acc, stateidx, statepattern, repeat, "-", offsets, patterns)
  else if w = "^"_1 then next(acc, 1, [STARTREC], repeat, "", offsets, patterns)
  else
   next(acc
   , stateidx
   , statepattern
   , repeat
   , ""
   , offsets
   , patterns >> 1 + (last.patterns + toint.w * if fld = "-"then-1 else 1 /if)
   )
 else if state = STARTREC then
  if w ∈ "="then next(acc, 1, [PATTERN], 1, "", offsets, patterns + empty:seq.int)
  else if w ∈ "size"then next(acc, 1, [SIZE], 1, "", offsets, patterns)
  else if w ∉ "-"then next(acc, 1, patterns_(toint.w), 1, "", offsets, patterns)
  else next(acc, 1, [CHANGE], repeat, [w], offsets, patterns)
 else if state = SIZE then
  let a3 = allocatespace.toint.w
  next(a3, 1, [STARTREC], 1, "", offsets >> 1 + [a3], patterns)
 else if state ∈ [CHANGE]then
  if length.fld < 3 then next(acc, 1, [CHANGE], repeat, fld + w, offsets, patterns)
  else if w ∈ "0"then
   let newacc = set(set(acc, 0), 0)
   next(newacc, 1, [STARTREC], 1, "", offsets + newacc, patterns)
  else
   let len = toint.w
   let typ = if last.fld ∈ "0"then 0 else blockseqtype:int
   let repeatno = 
    if last.fld ∈ "0"then len
    else
     let blksize = (toint.last.fld)
     (len + blksize - 1) / blksize
   next(set(set(acc, typ), len), 1, [-toint.fld_2], repeatno, "", offsets, patterns)
 else if state = WORD then
  let newacc = set(acc, hash.w)
  if stateidx = length.statepattern then
   next(newacc, 1, [STARTREC], repeat, "", offsets + newacc, patterns)
  else next(newacc, stateidx + 1, statepattern, repeat, fld, offsets, patterns)
 else if state = INT then
  if w ∈ "-"then next(acc, stateidx, statepattern, repeat, "-", offsets, patterns)
  else
   let newacc = set(acc, toint.w * if fld = "-"then-1 else 1)
   if stateidx = length.statepattern then
    next(newacc, 1, [STARTREC], repeat, "", offsets + newacc, patterns)
   else next(newacc, stateidx + 1, statepattern, repeat, fld, offsets, patterns)
 else if state = REAL then
  let xx = if length.fld = 2 ∧ first.fld ∈ "-"then 3 else 2
  if length.fld < xx then next(acc, stateidx, statepattern, repeat, fld + w, offsets, patterns)
  else
   let newacc = set(acc, representation.makereal(fld + w))
   if stateidx = length.statepattern then
    next(newacc, 1, [STARTREC], repeat, "", offsets + newacc, patterns)
   else next(newacc, stateidx + 1, statepattern, repeat, "", offsets, patterns)
 else if state = WORDS then
  if isempty.fld then next(acc, stateidx, statepattern, repeat, [w], offsets, patterns)
  else if w = first.fld then
   let newacc = set(acc, toptr(fld << 1))
   if stateidx = length.statepattern then
    next(newacc, 1, [STARTREC], repeat, "", offsets + newacc, patterns)
   else next(newacc, stateidx + 1, statepattern, repeat, fld, offsets, patterns)
  else next(acc, stateidx, statepattern, repeat, fld + w, offsets, patterns)
 else
  assert state < 0 report"state problem" + toword.state
  let newacc = 
   if state = -2 then set(acc, toint.w)
   else
    assert toint.w ≤ length.offsets report"format problem 1" + toword.state
    set(acc, offsets_(toint.w))
  if stateidx = length.statepattern then
   if repeat = 1 then next(newacc, 1, [STARTREC], repeat, "", offsets + newacc, patterns)
   else next(newacc, 1, statepattern, repeat - 1, "", offsets, patterns)
  else next(newacc, stateidx + 1, statepattern, repeat, fld, offsets, patterns)
/for(offsets_(length.offsets - 1)) 