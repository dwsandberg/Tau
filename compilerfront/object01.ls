Module object01

use LEBencoding

use UTF8

use bits

use seq.byte

use bitcast.int

use otherseq.int

use bitcast.seq.int

use seq.seq.int

use seq.mytype

use seq.seq.mytype

use set.mytype

use ptr

use bitcast.ptr

use seq.ptr

use stack.ptr

use standard

use symbol2

use encoding.tableentry

use seq.tableentry

use tausupport

use bitcast.word

Export type:tableentry

type tableentry is key:seq.int

function hash(a:tableentry) int hash.key.a

function =(a:tableentry, b:tableentry) boolean key.a = key.b

function %(i:byte) seq.word [toword.toint.i]

function %(i:tableentry) seq.word "/br^(key.i)"

Function formatTypeDef(defs0:seq.seq.mytype) seq.seq.int
let defs = fix5.defs0
for acc = empty:seq.seq.int, def ∈ defs
do
 if isseq.1#def then
  let idx = for idx = 1, d ∈ defs while 1#d ≠ parameter.1#def do idx + 1, idx,
  acc + [-idx]
 else
  for coded = empty:seq.int, t0 ∈ def << 1
  do
   let t = if isseq.t0 then parameter.t0 else t0
   for idx = 1, d ∈ defs while 1#d ≠ t do idx + 1,
   coded + if isseq.t0 then -idx else idx,
  acc + if isempty.coded then [n.acc + 1] else coded,
acc

function int0 int 2

function word0 int 3

function real0 int 4

function buildword int {1 <chars of word>} 1

function buildrecord int {2 rectyp <elements of record>} 2

function buildseq int {3 elementtyp <length of seq> <elements of seq>} 3

function buildtblrecord int {4 rectyp elements of record} 4

function buildtblseq int {5 rectyp <length of seq> elements of seq} 5

function buildblock int {6 elementyp <no of blocks> <length of seq> <elements of block seq>} 6

{The format is a group of records that descibe types followed by [-1] followed by build records. 

The first record is the root time. The next records with be [2], [3], [4] which represents the
types, word, and real. A type with fields of type int, seq.word, and real would be represented by [
2,-3, 4]. The absolute value of the elements is a pointer into records.Negative values represent
a seq type. 

When reconstructing objects, an object is built from each record. If the records is a buildword, buildtblrecord
or a buldtblseq then the result object is added as the last element in the table otherwise the result
object is placed on the stack. Elements of the record that are positive refer to and object in the
table and negative elements refer to objects on the stack. After the object is built, the element references
are pop from the stack. }

Function fix5(a0:seq.seq.mytype) seq.seq.mytype
let root = 1#a0
let a = [root, [typeint], [typeword], [typereal]] + a0 << 1
let singlerow =
 for singlerow = empty:seq.seq.mytype, row ∈ a
 do if n.row = 2 then singlerow + row else singlerow,
 singlerow,
close.
 if isempty.singlerow then
 a
 else
  {remove555 types not represented by a record}
  for result = empty:seq.seq.mytype, row2 ∈ a
  do result + for acc = [1#row2], t ∈ row2 << 1 do acc + sub(t, singlerow), acc
  for acc = empty:seq.seq.mytype, row ∈ result
  do if n.row = 2 ∧ not.isseq.1#row then acc else acc + row,
  acc

function close(x:seq.seq.mytype) seq.seq.mytype
{add types used but not defined}
for defs = empty:seq.mytype, used = empty:seq.mytype, def ∈ x
do next(
 defs + 1#def
 , used
  + 
   if isseq.1#def then
   [parameter.1#def]
   else
    for acc = empty:seq.mytype, d ∈ def << 1
    do if not.isseq.d then acc + d else if not.isseq.parameter.d then acc else acc + parameter.d,
    acc
)
let newdefs = toseq(asset.used \ asset.defs),
if isempty.newdefs then
x
else for acc = x, new ∈ toseq(asset.used \ asset.defs) do acc + [new], close.acc

function sub(t:mytype, singlerow:seq.seq.mytype) mytype
if t ∈ [typeint, typeword, typereal] then
t
else if isseq.t then
seqof.sub(parameter.t, singlerow)
else for acc = t, row ∈ singlerow do if t = 1#row then 1^row else acc, acc

Function outrec(inobj:ptr, allpatterns:seq.seq.int) seq.seq.int
allpatterns + [-1] + outrec(empty:seq.seq.int, inobj, allpatterns,-1)

function resulttype(packedsize:int, elementtypeidx:int) word
if elementtypeidx ∈ [word0, int0] then
1#"int"
else if elementtypeidx = real0 then
1#"real"
else packedsize#"ptr packed2 packed3 packed4 packed5 packed6"

function outrec(
 finished0:seq.seq.int
 , inobj:ptr
 , allpatterns:seq.seq.int
 , patternidx:int
) seq.seq.int
let pattern = if patternidx < 0 then empty:seq.int else patternidx#allpatterns,
if patternidx < 0 ∨ n.pattern = 1 ∧ 1#pattern < 0 then
 let eletypeidx = if patternidx < 0 then -patternidx else -1#patternidx#allpatterns
 let elepattern = packedpattern(eletypeidx#allpatterns, eletypeidx)
 let packedsize = if n.elepattern > 6 then 1 else n.elepattern
 let obj = packobject(resulttype(packedsize, eletypeidx), inobj)
 let seqlen = n.bitcast:seq.int(obj),
  if fld:int(obj, 0) ∈ [0, 1] then
  outrecflds(
   buildseq
   , {fldtypes} constantseq(seqlen * packedsize, elepattern)
   , [buildseq, eletypeidx, n.bitcast:seq.int(obj)]
   , finished0
   , obj
   , allpatterns
  )
  else
   let blocksize = n.fld:seq.int(obj, 2)
   let noblocks = (seqlen + blocksize - 1) / blocksize,
   outrecflds(
    buildblock
    , constantseq(noblocks, patternidx)
    , [buildblock, eletypeidx, noblocks, seqlen]
    , finished0
    , obj
    , allpatterns
   )
else outrecflds(buildrecord, pattern, [buildrecord, patternidx], finished0, inobj, allpatterns)

function outrecflds(
 buildtype:int
 , fldtypes:seq.int
 , start:seq.int
 , finished0:seq.seq.int
 , obj:ptr
 , allpatterns:seq.seq.int
) seq.seq.int
for
 acc = start
 , idx = if buildtype = buildrecord then 0 else 2
 , stkcount = 0
 , finished = finished0
 , typ ∈ fldtypes
do
 if typ ∈ [int0, real0] then
 next(acc + fld:int(obj, idx), idx + 1, stkcount, finished)
 else if typ = word0 then
  let te = [buildword] + tointseq.decodeword.fld:word(obj, idx)
  let maxencoding = n.encodingdata:tableentry
  let w = addorder.tableentry.te,
  next(acc + w, idx + 1, stkcount, if maxencoding < w then finished + te else finished)
 else
  let t = outrec(finished, fld:ptr(obj, idx), allpatterns, typ),
   if 1#1^t ∈ [buildtblrecord, buildtblseq] then
    let maxencoding = n.encodingdata:tableentry
    let w = addorder.tableentry.1^t,
    next(acc + w, idx + 1, stkcount, if w > maxencoding then t else t >> 1)
   else next(acc + -(stkcount + 1), idx + 1, stkcount + 1, t),
finished
 + 
 if stkcount > 0 then
 adjuststkcounts(acc, fldtypes, stkcount)
 else if buildtype = buildrecord ∧ n.acc < 10 then
 [buildtblrecord] + acc << 1
 else if buildtype = buildseq ∧ (n.acc < 10 ∨ 2#acc = word0 ∧ n.acc < 300) then
 [buildtblseq] + acc << 1
 else acc

function dumptable seq.word
for txt = "/br tableentry", r ∈ encodingdata:tableentry do txt + %.r,
txt

Function dump(finished:seq.seq.int) seq.word
for txt = "/br finished", r ∈ finished do txt + "/br" + %.r,
txt

Function inrec(inrecs:seq.seq.int) ptr
let allpatterns = for idx = 0, pat ∈ inrecs while 1#pat ≠ -1 do idx + 1, subseq(inrecs, 1, idx)
for stk = empty:stack.ptr, map = empty:seq.int, rec ∈ inrecs << (n.allpatterns + 1)
do
 if 1#rec = buildword then
  {add word entry to map}
  next(stk, (for acc = empty:seq.char, i ∈ rec << 1 do acc + char.i, map + hash.encodeword.acc))
 else if 1#rec = buildblock then
  let noblocks = 3#rec
  let eletypeidx = 2#rec
  let seqelepat = eletypeidx#allpatterns
  let elepattern = packedpattern(seqelepat, eletypeidx)
  let obj = allocatespace(noblocks + 2)
  let firstp = set(set(obj, blocktype.resulttype(n.elepattern, eletypeidx)), 4#rec)
  let newstk =
   for p = firstp, m = 0, val ∈ rec << 4
   do
    if val > 0 then
    next(set(p, val#map), m)
    else next(set(p, undertop(stk,-val - 1)), if val < m then val else m),
   push(pop(stk,-m), obj),
  next(newstk, map)
 else
  let newstk =
   if 1#rec = buildseq ∨ 1#rec = buildtblseq then
    let eletypeidx = 2#rec
    let seqelepat = eletypeidx#allpatterns
    let elepattern = packedpattern(seqelepat, eletypeidx)
    let seqlen = 3#rec
    let packedsize = n.elepattern
    let fldtypes = constantseq(seqlen * packedsize, elepattern)
    let blksize = 100
    let myblksz = if n.fldtypes + 3 ≤ blksize then blksize else blksize / packedsize * packedsize
    let obj = allocatespace(min(n.fldtypes, myblksz) + 2)
    for
     p = set(set(obj, if packedsize = 1 then 0 else 1), min(seqlen, myblksz / packedsize))
     , i = 4
     , m = 0
     , objs = empty:seq.ptr
     , typ ∈ fldtypes
    do
     let newblksize =
      if i - 4 = myblksz * (n.objs + 1) then
      min(n.fldtypes - myblksz * (n.objs + 1), myblksz)
      else 0
     assert newblksize < 8000 report "XXX^(newblksize)"
     let newobjs = if newblksize = 0 then objs else objs + allocatespace(newblksize + 2)
     let newp =
      if newblksize = 0 then
      p
      else set(set(1^newobjs, if packedsize = 1 then 0 else 1), newblksize / packedsize)
     let val = i#rec,
      if typ ∈ [int0, real0] then
      next(set(newp, val), i + 1, m, newobjs)
      else if val > 0 then
      next(set(newp, val#map), i + 1, m, newobjs)
      else next(set(newp, undertop(stk,-val - 1)), i + 1, if val < m then val else m, newobjs)
    let resulttype = resulttype(packedsize, eletypeidx)
    for acc = obj, o ∈ objs do cat(acc, o, resulttype)
    let fx = push(pop(stk,-m), acc)
    assert not.isempty.fx report "??",
    fx
   else
    assert 1#rec ∈ [buildtblrecord, buildrecord] report "PROBLEM object01"
    {buildrecord}
    let pattern = (2#rec)#allpatterns
    assert n.pattern < 8000 report "to big of a pattern"
    let obj = allocatespace.n.pattern
    for p = obj, i = 3, m = 0, typ ∈ pattern
    do
     let val = i#rec,
      if typ ∈ [int0, real0] then
      next(set(p, val), i + 1, m)
      else if val > 0 then
      next(set(p, val#map), i + 1, m)
      else next(set(p, undertop(stk,-val - 1)), i + 1, if val < m then val else m),
    push(pop(stk,-m), obj),
   if 1#rec ∈ [buildtblseq, buildtblrecord] then
   next(pop.newstk, map + bitcast:int(top.newstk))
   else next(newstk, map),
if isempty.stk then bitcast:ptr(1^map) else top.stk

function adjuststkcounts(rec:seq.int, fldtypes:seq.int, stkcount:int) seq.int
let k = n.rec - n.fldtypes
for acc = subseq(rec, 1, k), i = k + 1, typ ∈ fldtypes
do
 let val = i#rec,
 next(
  if typ ∈ [int0, real0, word0] ∨ val > 0 then
  acc + val
  else acc + (-stkcount - val - 1)
  , i + 1
 ),
acc

Function encode2(data:seq.seq.int) seq.byte
for all = empty:seq.byte, rec ∈ data
do
 all
  + 
  for pos = true, j ∈ rec while pos do j ≥ 0,
   if pos then
   let acc = LEBu.rec, LEBu(n.acc * 2) + acc
   else let acc = LEBs.rec, LEBu(n.acc * 2 + 1) + acc,
LEBu.n.all + all

Function inrec(b:seq.byte) ptr inrec.decode2.b

Function decode2(b:seq.byte) seq.seq.int
let len = decodeLEBu(b, 1)
let end = next.len + value.len
for all = empty:seq.seq.int, next = next.len, t ∈ constantseq(value.len, 0)
while next < end
do
 let r = decodeLEBu(b, next)
 let val = value.r
 let endplace = next.r + val / 2
 let pos = val mod 2 = 0,
 next(
  for acc = empty:seq.int, place = next.r, t2 ∈ constantseq(val, 0)
  while place < endplace
  do
   let x = if pos then decodeLEBu(b, place) else decodeLEBs(b, place),
   next(acc + value.x, next.x),
  all + acc
  , endplace
 ),
all

-------------------------------

function packedpattern(seqelementpat:seq.int, eletypeidx:int) seq.int
if
 not.between(n.seqelementpat, 2, {must match packed seqs in implementation} 6)
  ∨ 1#seqelementpat = 0
then
[eletypeidx]
else seqelementpat 