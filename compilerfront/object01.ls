Module object01

use LEBencoding

use UTF8

use bits

use seq.byte

use bitcast.int

use seq1.int

use seq.int

use bitcast.seq.int

use seq.seq.int

use seq.mytype

use seq.seq.mytype

use set.mytype

use seq.packed2

use bitcast.seq.packed2

use seq.packed3

use bitcast.seq.packed3

use seq.packed4

use bitcast.seq.packed4

use seq.packed5

use bitcast.seq.packed5

use seq.packed6

use bitcast.seq.packed6

use ptr

use bitcast.ptr

use seq.ptr

use bitcast.seq.ptr

use stack.ptr

use seq.real

use bitcast.seq.real

use standard

use symbol1

use encoding.tableentry

use seq.tableentry

use tausupport

use bitcast.word

Export type:tableentry

type tableentry is key:seq.int

function hash(a:tableentry) int hash.key.a

function =(a:tableentry, b:tableentry) boolean key.a = key.b

function %(i:tableentry) seq.word "/br:(key.i)"

Function formatTypeDef(defs0:seq.seq.mytype) seq.seq.int
let defs = fix5.defs0
for acc = empty:seq.seq.int, def ∈ defs
do
 if isseq.def sub 1 then
  let idx =
   for idx = 1, d ∈ defs while d sub 1 ≠ parameter.def sub 1 do idx + 1,
   idx,
  acc + [-idx]
 else
  for coded = empty:seq.int, t0 ∈ def << 1
  do
   let t = if isseq.t0 then parameter.t0 else t0
   for idx = 1, d ∈ defs while d sub 1 ≠ t do idx + 1,
   coded + if isseq.t0 then-idx else idx,
  acc + if isempty.coded then [n.acc + 1] else coded,
acc

function int0 int 2

function word0 int 3

function real0 int 4

function buildword int
{1 <chars of word>}
1

function buildrecord int
{2 rectyp <elements of record>}
2

function buildseq int
{3 elementtyp <length of seq> <elements of seq>}
3

function buildtblrecord int
{4 rectyp elements of record}
4

function buildtblseq int
{5 rectyp <length of seq> elements of seq}
5

function buildblock int
{6 elementyp <no of blocks> <length of seq> <elements of block seq>}
6

{The format is a group of records that descibe types followed by [-1] followed by build records. 

The first record is the root time. The next records with be [2], [3], [4] which represents the types, word, and real. A type with fields of type int, seq.word, and real would be represented by [2,-3, 4]. The absolute value of the elements is a pointer into records.Negative values represent a seq type. 

When reconstructing objects, an object is built from each record. If the records is a buildword, buildtblrecord or a buldtblseq then the result object is added as the last element in the table otherwise the result object is placed on the stack. Elements of the record that are positive refer to and object in the table and negative elements refer to objects on the stack. After the object is built, the element references are pop from the stack. }

Function fix5(a0:seq.seq.mytype) seq.seq.mytype
let root = a0 sub 1
let a = [root, [typeint], [typeword], [typereal]] + a0 << 1
for singlerow = empty:seq.seq.mytype, row ∈ a
do if n.row = 2 then singlerow + row else singlerow,
close(
 if isempty.singlerow then a
 else
  {remove types not represented by a record}
  for result = empty:seq.seq.mytype, row2 ∈ a
  do
   result
    + for acc = [row2 sub 1], t ∈ row2 << 1
   do acc + substitute(t, singlerow),
   acc
  for acc = empty:seq.seq.mytype, row ∈ result
  do if n.row = 2 ∧ not.isseq.row sub 1 then acc else acc + row,
  acc
)

function close(x:seq.seq.mytype) seq.seq.mytype
{add types used but not defined}
for defs = empty:seq.mytype, used = empty:seq.mytype, def ∈ x
do
 next(
  defs + def sub 1
  , used
   + (if isseq.def sub 1 then [parameter.def sub 1]
  else
   for acc = empty:seq.mytype, d ∈ def << 1
   do if not.isseq.d then acc + d else if not.isseq.parameter.d then acc else acc + parameter.d,
   acc
  )
 )
let newdefs = toseq(asset.used \ asset.defs),
if isempty.newdefs then x
else
 for acc = x, new ∈ toseq(asset.used \ asset.defs)
 do acc + [new],
 close.acc

function substitute(t:mytype, singlerow:seq.seq.mytype) mytype
if t ∈ [typeint, typeword, typereal] then t
else if isseq.t then seqof.substitute(parameter.t, singlerow)
else
 for acc = t, row ∈ singlerow
 do if t = row sub 1 then row sub n.row else acc,
 acc

Function outrec(inobj:ptr, allpatterns:seq.seq.int) seq.seq.int
allpatterns + [-1] + outrec(empty:seq.seq.int, inobj, allpatterns,-1)

function resulttype(packedsize:int, elementtypeidx:int) word
if elementtypeidx ∈ [word0, int0] then "int" sub 1
else if elementtypeidx = real0 then "real" sub 1
else "ptr packed2 packed3 packed4 packed5 packed6" sub packedsize

function outrec(
finished0:seq.seq.int
, inobj:ptr
, allpatterns:seq.seq.int
, patternidx:int
) seq.seq.int
let pattern = if patternidx < 0 then empty:seq.int else allpatterns sub patternidx,
if patternidx < 0 ∨ n.pattern = 1 ∧ pattern sub 1 < 0 then
 let eletypeidx = if patternidx < 0 then-patternidx else-(allpatterns sub patternidx) sub 1
 let elepattern = packedpattern(allpatterns sub eletypeidx, eletypeidx)
 let packedsize = if n.elepattern > 6 then 1 else n.elepattern
 let obj = packobject(resulttype(packedsize, eletypeidx), inobj),
 let seqlen = n.bitcast:seq.int(obj),
 if fld:int(obj, 0) ∈ [0, 1] then
  outrecflds(
   buildseq
   , {fldtypes} patternseq(seqlen * packedsize, elepattern)
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
 if typ ∈ [int0, real0] then next(acc + fld:int(obj, idx), idx + 1, stkcount, finished)
 else if typ = word0 then
  let te = [buildword] + tointseq.decodeword.fld:word(obj, idx)
  let maxencoding = n.encodingdata:tableentry,
  let w = addorder.tableentry.te,
  next(acc + w, idx + 1, stkcount, if maxencoding < w then finished + te else finished)
 else
  let t = outrec(finished, fld:ptr(obj, idx), allpatterns, typ)
  let last = t sub n.t,
  if last sub 1 ∈ [buildtblrecord, buildtblseq] then
   let maxencoding = n.encodingdata:tableentry
   let w = addorder.tableentry.last,
   next(acc + w, idx + 1, stkcount, if w > maxencoding then t else t >> 1)
  else next(acc + -(stkcount + 1), idx + 1, stkcount + 1, t),
finished
 + if stkcount > 0 then adjuststkcounts(acc, fldtypes, stkcount)
else if buildtype = buildrecord ∧ n.acc < 10 then [buildtblrecord] + acc << 1
else if buildtype = buildseq ∧ (n.acc < 10 ∨ acc sub 2 = word0 ∧ n.acc < 300) then [buildtblseq] + acc << 1
else acc

function dumptable seq.word
for txt = "/br tableentry", r ∈ encodingdata:tableentry
do txt + %.r,
txt

Function dump(finished:seq.seq.int) seq.word
for txt = "/br finished", r ∈ finished
do txt + "/br" + %.r,
txt

Function inrec(inrecs:seq.seq.int) ptr
let allpatterns =
 for idx = 0, pat ∈ inrecs while pat sub 1 ≠-1 do idx + 1,
 subseq(inrecs, 1, idx)
for stk = empty:stack.ptr, map = empty:seq.int, rec ∈ inrecs << (n.allpatterns + 1)
do
 if rec sub 1 = buildword then
  {add word entry to map}
  next(
   stk
   , for acc = empty:seq.char, i ∈ rec << 1 do acc + char.i,
   map + hash.encodeword.acc
  )
 else if rec sub 1 = buildblock then
  let noblocks = rec sub 3
  let eletypeidx = rec sub 2
  let seqelepat = allpatterns sub eletypeidx
  let elepattern = packedpattern(seqelepat, eletypeidx)
  let obj = allocatespace(noblocks + 2)
  let firstp = set(set(obj, blocktype.resulttype(n.elepattern, eletypeidx)), rec sub 4),
  let newstk =
   for p = firstp, m = 0, val ∈ rec << 4
   do
    if val > 0 then next(set(p, map sub val), m)
    else next(set(p, undertop(stk,-val - 1)), if val < m then val else m),
   push(pop(stk,-m), obj),
  next(newstk, map)
 else
  let newstk =
   if rec sub 1 = buildseq ∨ rec sub 1 = buildtblseq then
    let eletypeidx = rec sub 2
    let seqelepat = allpatterns sub eletypeidx
    let elepattern = packedpattern(seqelepat, eletypeidx)
    let seqlen = rec sub 3
    let packedsize = n.elepattern
    let fldtypes = patternseq(seqlen * packedsize, elepattern)
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
      if i - 4 = myblksz * (n.objs + 1) then min(n.fldtypes - myblksz * (n.objs + 1), myblksz)
      else 0
     assert newblksize < 8000 report "XXX:(newblksize)"
     let newobjs = if newblksize = 0 then objs else objs + allocatespace(newblksize + 2)
     let newp =
      if newblksize = 0 then p
      else set(set(newobjs sub n.newobjs, if packedsize = 1 then 0 else 1), newblksize / packedsize),
     let val = rec sub i,
     if typ ∈ [int0, real0] then next(set(newp, val), i + 1, m, newobjs)
     else if val > 0 then next(set(newp, map sub val), i + 1, m, newobjs)
     else next(set(newp, undertop(stk,-val - 1)), i + 1, if val < m then val else m, newobjs)
    let resulttype = resulttype(packedsize, eletypeidx)
    for acc = obj, o ∈ objs do cat(acc, o, resulttype)
    let fx = push(pop(stk,-m), acc),
    assert not.isempty.fx report "??",
    fx
   else
    assert rec sub 1 ∈ [buildtblrecord, buildrecord] report "PROBLEM object01"
    {buildrecord}
    let pattern = allpatterns sub (rec sub 2)
    assert n.pattern < 8000 report "to big of a pattern"
    let obj = allocatespace.n.pattern,
    for p = obj, i = 3, m = 0, typ ∈ pattern
    do
     let val = rec sub i,
     if typ ∈ [int0, real0] then next(set(p, val), i + 1, m)
     else if val > 0 then next(set(p, map sub val), i + 1, m)
     else next(set(p, undertop(stk,-val - 1)), i + 1, if val < m then val else m),
    push(pop(stk,-m), obj),
  if rec sub 1 ∈ [buildtblseq, buildtblrecord] then next(pop.newstk, map + bitcast:int(top.newstk))
  else next(newstk, map),
if isempty.stk then bitcast:ptr(map sub n.map) else top.stk

function adjuststkcounts(rec:seq.int, fldtypes:seq.int, stkcount:int) seq.int
let k = n.rec - n.fldtypes
for acc = subseq(rec, 1, k), i = k + 1, typ ∈ fldtypes
do
 let val = rec sub i,
 next(
  if typ ∈ [int0, real0, word0] ∨ val > 0 then acc + val
  else acc + (-stkcount - val - 1)
  , i + 1
 ),
acc

Function encode2(data:seq.seq.int) seq.byte
for all = empty:seq.byte, rec ∈ data
do
 all
  + for pos = true, j ∈ rec while pos do j ≥ 0,
 if pos then
  let acc = LEBu.rec,
  LEBu(n.acc * 2) + acc
 else
  let acc = LEBs.rec,
  LEBu(n.acc * 2 + 1) + acc,
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
 let endplace = next.r + val / 2,
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
if not.between(n.seqelementpat, 2, {must match packed seqs in implementation} 6)
∨ seqelementpat sub 1 = 0 then [eletypeidx]
else seqelementpat

Function packobject(typ:word, obj:ptr) ptr
if typ ∈ "int" then toptr.packed.bitcast:seq.int(obj)
else if typ ∈ "real" then toptr.packed.bitcast:seq.real(obj)
else if typ ∈ "ptr" then toptr.packed.bitcast:seq.ptr(obj)
else if typ ∈ "packed2" then toptr.packed.bitcast:seq.packed2(obj)
else if typ ∈ "packed3" then toptr.packed.bitcast:seq.packed3(obj)
else if typ ∈ "packed4" then toptr.packed.bitcast:seq.packed4(obj)
else if typ ∈ "packed5" then toptr.packed.bitcast:seq.packed5(obj)
else
 assert typ ∈ "packed6" report "packing not found" + typ,
 toptr.packed.bitcast:seq.packed6(obj)

Function cat(obj1:ptr, obj2:ptr, typ:word) ptr
if typ ∈ "int" then toptr(bitcast:seq.int(obj1) + bitcast:seq.int(obj2))
else if typ ∈ "real" then toptr(bitcast:seq.real(obj1) + bitcast:seq.real(obj2))
else if typ ∈ "ptr" then toptr(bitcast:seq.ptr(obj1) + bitcast:seq.ptr(obj2))
else if typ ∈ "packed2" then toptr(bitcast:seq.packed2(obj1) + bitcast:seq.packed2(obj2))
else if typ ∈ "packed3" then toptr(bitcast:seq.packed3(obj1) + bitcast:seq.packed3(obj2))
else if typ ∈ "packed4" then toptr(bitcast:seq.packed4(obj1) + bitcast:seq.packed4(obj2))
else if typ ∈ "packed5" then toptr(bitcast:seq.packed5(obj1) + bitcast:seq.packed5(obj2))
else
 assert typ ∈ "packed6" report "packing cat not found" + typ,
 toptr(bitcast:seq.packed6(obj1) + bitcast:seq.packed6(obj2))
 
