Module object01

use LEBencoding

use UTF8

use bits

use packit

use ptr

use standard

use symbol2

use seq.byte

use bitcast.int

use otherseq.int

use seq.int

use seq.mytype

use set.mytype

use bitcast.ptr

use seq.ptr

use stack.ptr

use encoding.tableentry


use bitcast.word

use seq.seq.byte

use bitcast.seq.int

use seq.seq.int

use seq.seq.mytype

use bitcast.seq.word


Export type:tableentry

type tableentry is key:seq.int 

function hash(a:tableentry)int hash.key.a

function =(a:tableentry, b:tableentry)boolean key.a = key.b

function %(i:byte)seq.word[toword.toint.i]

function %(i:tableentry)seq.word "/br"+%.key.i

use otherseq.tableentry

Function formatTypeDef(defs0:seq.seq.mytype)seq.seq.int
let defs = fix5.defs0
for acc = empty:seq.seq.int, def ∈ defs do
 if isseq.first.def then
  let idx = 
   for idx = 1, d ∈ defs while first.d ≠ parameter.first.def do idx + 1 /for(idx)
  acc + [ -idx]
 else
  for coded = empty:seq.int, t0 ∈ def << 1 do
   let t=if isseq.t0 then parameter.t0 else t0
   for idx = 1, d ∈ defs while first.d ≠ t do idx + 1 
   /for( coded+if isseq.t0 then -idx else idx)
  /for(acc + if isempty.coded then[length.acc + 1]else coded /if)
/for(acc)


function word0 int 3

function int0 int 2

function real0 int 4


Function fix5(a0:seq.seq.mytype)seq.seq.mytype
{ if length.root = 2 ∧ isseq.root_2 then[[root_2, parameter.root_2]] + a0 else } 
let root = first.a0
let a = [ root,
[typeint] 
,[typeword] 
,[typereal] 
]  +a0 << 1
let singlerow = 
 for singlerow = empty:seq.seq.mytype, row ∈ a do
  if length.row = 2 then{∧ not.isseq.last.row ∧ not.isseq.first.row then}singlerow + row
  else singlerow
 /for(singlerow)
close.if isempty.singlerow then a
else
 {remove types not represented by a record}
 for result = empty:seq.seq.mytype, row2 ∈ a do
  result
  + for acc = [first.row2], t ∈ row2 << 1 do acc + sub(t, singlerow)/for(acc)
 /for(for acc = empty:seq.seq.mytype, row ∈ result do
  if length.row = 2 ∧ not.isseq.row_1 then acc else acc + row
 /for(acc))


function close(x:seq.seq.mytype)seq.seq.mytype
{add types used but not defined}
for defs = empty:seq.mytype, used = empty:seq.mytype, def ∈ x do
 next(defs + first.def
 , used + if isseq.first.def then [ parameter.first.def] else 
  for acc=empty:seq.mytype,    d /in  def << 1 do
   if not.isseq.d then acc +d else if not.isseq.parameter.d then acc else acc+parameter.d
   /for(acc)
 )
/for(let newdefs = toseq(asset.used \ asset.defs)
if isempty.newdefs then x
else close.for acc = x, new ∈ toseq(asset.used \ asset.defs)do acc + [new]/for(acc)/if)

function sub(t:mytype, singlerow:seq.seq.mytype)mytype
if t ∈ [typeint, typeword, typereal]then t
else if isseq.t then seqof.sub(parameter.t, singlerow)
else
 for acc = t, row ∈ singlerow do if t = first.row then last.row else acc /for(acc)

Function outrec(inobj:ptr, allpatterns:seq.seq.int)seq.seq.int
allpatterns + [-1]
+ outrec(empty:seq.seq.int, inobj, allpatterns, -1)

function resulttype(packedsize:int, elementtypeidx:int)word
 if elementtypeidx /in [word0,int0] then first."int" else if elementtypeidx =real0 then first."real"  
 else"ptr packed2 packed3 packed4 packed5 packed6"_(packedsize )  


function outrec(finished0:seq.seq.int, inobj:ptr, allpatterns:seq.seq.int, patternidx:int)seq.seq.int
let pattern = if patternidx < 0 then empty:seq.int else  allpatterns_patternidx 
if  patternidx < 0 /or length.pattern=1 /and first.pattern < 0 then
 let eletypeidx = if patternidx  < 0 then -patternidx  else  -first.allpatterns_patternidx 
 let elepattern = packedpattern(allpatterns_eletypeidx, eletypeidx)
 let packedsize = if length.elepattern > 6 then 1 else length.elepattern
  let obj = packobject(resulttype(packedsize, eletypeidx), inobj)
  assert length.allpatterns < 10 /or  patternidx /in [-1] report "JK"+%.packedsize+%.eletypeidx+"/br"+%.elepattern+dump.allpatterns
  +resulttype(packedsize, eletypeidx)
 let seqlen = length.bitcast:seq.int(obj)
 let fldtypes = constantseq(seqlen * packedsize, elepattern)
let t=hjk(fldtypes
 , [buildseq, eletypeidx, length.bitcast:seq.int(obj)]
 , finished0
 , obj
 , allpatterns
 )
t
else hjk(pattern, [buildrecord, patternidx], finished0,  inobj, allpatterns)

function hjk(fldtypes:seq.int
, start:seq.int
, finished0:seq.seq.int
, obj:ptr
, allpatterns:seq.seq.int
)seq.seq.int
for acc = start
, idx = if first.start = buildseq then 2 else 0
, stkcount = 0
, finished = finished0
 , typ ∈ fldtypes
do
  if typ ∈ [int0, real0]then next(acc + fld:int(obj, idx), idx + 1, stkcount, finished )
 else if typ = word0 then
   let te=[buildword]+tointseq.decodeword.fld:word(obj, idx)
   let maxencoding=length.encodingdata:tableentry
  let w=addorder.tableentry(te)
     next(acc + w
   , idx + 1
   , stkcount
   , if maxencoding < w then finished + te else finished
   )
 else
   let t = outrec(finished, fld:ptr(obj, idx), allpatterns, typ)
    if first.last.t /in [buildtblrecord , buildtblseq ] then 
         let maxencoding=length.encodingdata:tableentry
        let w=addorder.tableentry(last.t)
            next(acc+w,idx+1,stkcount,if w > maxencoding   then  t  else t >> 1    )
      else
  next(acc + -(stkcount + 1), idx + 1, stkcount + 1, t )
/for(
finished + if stkcount > 0 then preprocess(acc, fldtypes, stkcount)else 
 if  length.acc < 10 /or subseq(acc,1,2)=[buildseq,word0] then
    [if first.acc=buildrecord then buildtblrecord else buildtblseq ]+ acc << 1
 else acc
)

function dumptable seq.word
 for    txt="/br tableentry",   r /in encodingdata:tableentry do
  txt+ %.r /for(txt)

function dump(finished:seq.seq.int) seq.word
 for    txt="/br finished",   r /in finished do
  txt+ "/br"+%.r /for(txt)
 


use seq.tableentry

function buildword int{1 <chars of word>}1

function buildrecord int{2 rectyp elements of record}2

function buildseq int{3 elementtyp <elements of seq>}3

function buildtblrecord int {4 rectyp elements of record}4 

function buildtblseq int {5 rectyp elements of record}5 



Function inrec(inrecs:seq.seq.int)ptr
let allpatterns = 
 for idx = 0, pat ∈ inrecs while first.pat ≠ -1 do idx + 1 /for(subseq(inrecs, 1, idx))
for stk = empty:stack.ptr, map = empty:seq.int, rec ∈ inrecs << (length.allpatterns + 1)do
 if first.rec = buildword then
  {add word entry to map}
  next(stk
  , map
  + hash.encodeword.for acc = empty:seq.char, i ∈ rec << 1 do acc + char.i /for(acc)
  )
 else
  {assert length.fldtypes < 8151 report"object too big"+toword.length.fldtypes 
  }
  let newstk = 
   if rec_1 = buildseq /or rec_1 = buildtblseq then
    let eletypeidx = rec_2
    let seqelepat = allpatterns_eletypeidx
    let elepattern = packedpattern(seqelepat, eletypeidx)
    let seqlen = rec_3
    let packedsize = length.elepattern
    let fldtypes = constantseq(seqlen * packedsize, elepattern)
     let blksize = 20
    let myblksz = 
     if length.fldtypes + 3 ≤ blksize then blksize else blksize / packedsize * packedsize
    let obj = allocatespace(min(length.fldtypes, myblksz) + 2)
    for p = set(set(obj, if packedsize = 1 then 0 else 1)
    , min(seqlen, myblksz / packedsize)
    )
    , i = 4
    , m = 0
    , objs = empty:seq.ptr
    , typ ∈ fldtypes
    do
     let newblksize = 
      if i - 4 = myblksz * (length.objs + 1)then min(length.fldtypes - myblksz * (length.objs + 1), myblksz)
      else 0
     let newobjs = if newblksize = 0 then objs else objs + allocatespace(newblksize + 2)
     let newp = 
      if newblksize = 0 then p
      else set(set(last.newobjs, if packedsize = 1 then 0 else 1), newblksize)
     let val = rec_i
     if typ ∈ [int0, real0]then next(set(newp, val), i + 1, m, newobjs)
     else if val > 0 then next(set(newp, map_val), i + 1, m, newobjs)
     else
      next(set(newp, undertop(stk, -val - 1))
      , i + 1
      , if val < m then val else m
      , newobjs
      )
    /for(  let resulttype = resulttype(packedsize,eletypeidx)
        for acc = obj, o ∈ objs do cat(acc, o, resulttype)
    /for(let fx=push(pop(stk, -m), acc)
         assert not.isempty.fx report "??"
         fx))
   else
    {buildrecord}
    let pattern = allpatterns_(rec_2)
    let obj = allocatespace.length.pattern
    for p = obj, i = 3, m = 0, typ ∈ pattern do
     let val = rec_i
     if typ ∈ [int0, real0]then next(set(p, val), i + 1, m)
     else if val > 0 then next(set(p, map_val), i + 1, m)
     else
      next(set(p, undertop(stk, -val - 1)), i + 1, if val < m then val else m)
    /for(push(pop(stk, -m), obj))
    if first.rec /in[buildtblseq ,buildtblrecord] then
      next(pop(newstk),map+bitcast:int(top.newstk))
    else 
     next(newstk, map)
/for(top.stk)

function preprocess(rec:seq.int, fldtypes:seq.int, stkcount:int)seq.int
let k = length.rec - length.fldtypes
for acc = subseq(rec, 1, k), i = k + 1, typ ∈ fldtypes do
 let val = rec_i
 next(if typ ∈ [int0, real0, word0] ∨ val > 0 then acc + val else acc + (-stkcount - val - 1)
 , i + 1
 )
/for(acc)

Function encode2(data:seq.seq.int)seq.byte
for all = empty:seq.byte, rec ∈ data do
 all
 + for pos = true, j ∈ rec while pos do j ≥ 0 /for(if pos then
  for acc = empty:seq.byte, i ∈ rec do acc + LEBu.i /for(LEBu(length.acc * 2) + acc)
 else
  for acc = empty:seq.byte, i ∈ rec do acc + LEBs.i /for(LEBu(length.acc * 2 + 1) + acc)/if)
/for(LEBu.length.all + all)

Function decode2(b:seq.byte)seq.seq.int
let len = decodeLEBu(b, 1)
let end = next.len + value.len
{assert false report %.end+%.length.b}
for all = empty:seq.seq.int, next = next.len, t ∈ constantseq(value.len, 0)
while next < end
do let r = decodeLEBu(b, next)
let val = value.r
let endplace = next.r + val / 2
let pos = val mod 2 = 0
next(for acc = empty:seq.int, place = next.r, t2 ∈ constantseq(val, 0)
while place < endplace
do let x = if pos then decodeLEBu(b, place)else decodeLEBs(b, place)
next(acc + value.x, next.x)
/for(all + acc)
, endplace
)
/for(all)

function vector(a:seq.char)seq.int for acc = empty:seq.int, c ∈ a do acc + toint.c /for(acc)

____________________________________



function packedpattern(seqelementpat:seq.int, eletypeidx:int)seq.int
if not.between(length.seqelementpat, 2, {must match packed seqs in implementation}6)
∨ first.seqelementpat = 0 then
 [eletypeidx]
else seqelementpat     

    
   
module packit


use tausupport

use standard

use bitcast.seq.int

use seq.real

use seq.ptr

use seq.packed3

use seq.packed2


use bitcast.seq.real


use bitcast.seq.ptr

use bitcast.seq.packed3

use bitcast.seq.packed2

use bitcast.seq.packed6


Function cat(obj1:ptr,obj2:ptr,typ:word) ptr
   if typ /in "int" then toptr(bitcast:seq.int(obj1)+bitcast:seq.int(obj2))
 else if typ /in "real" then toptr(bitcast:seq.real(obj1)+bitcast:seq.real(obj2))
 else if typ /in "ptr" then 
  toptr(bitcast:seq.ptr(obj1)+bitcast:seq.ptr(obj2))
 else if typ /in "packed2"  then
  toptr(bitcast:seq.packed2(obj1)+bitcast:seq.packed2(obj2))
 else assert typ /in "packed3" report "packing cat not found"+typ
  toptr(bitcast:seq.packed3(obj1)+bitcast:seq.packed3(obj2))



Function packobject(typ:word,obj:ptr) ptr
  if typ /in "int" then toptr.blockIt.bitcast:seq.int(obj)
 else if typ /in "real" then toptr.blockIt.bitcast:seq.real(obj)
 else if typ /in "ptr" then toptr.blockIt.bitcast:seq.ptr(obj)
 else if typ /in "packed2" then 
    assert false report "here"+%.length.bitcast:seq.packed2(obj)
  let z=toptr.blockIt.bitcast:seq.packed2(obj)
     z
 else if typ /in "packed6" then 
  toptr.blockIt.bitcast:seq.packed6(obj)
 else 
 assert typ /in "packed3" report "packing not found"+typ
  toptr.blockIt.bitcast:seq.packed3(obj)
  

module objectio.T

use object01 

use standard

use bitcast.T

use seq.mytype

use symbol2


use seq.seq.int

use seq.byte

use bits

use bitcast.seq.T


Builtin typestructure:T seq.seq.mytype


Function outbytes:T(try:seq.T) seq.byte 
let pat=formatTypeDef.typestructure:T
 encode2.outrec(toptr.try,pat)

Function inbytes:T(in:seq.byte) seq.T 
 bitcast:seq.T(inrec.decode2.in) 



 