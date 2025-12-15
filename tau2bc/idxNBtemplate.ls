Module idxNBtemplate

use codetemplates

use encoding.idxNBtemplate

use seq.idxNBtemplate

use internalbc

use llvm

use seq.match5

use mytype

use seq1.mytype

use standard

use symbol1

Export type:idxNBtemplate

Export para(idxNBtemplate) mytype

Export regcount(idxNBtemplate) int

Export templates(idxNBtemplate) seq.match5

type idxNBtemplate is para:mytype, templates:seq.match5, regcount:int

function =(a:idxNBtemplate, b:idxNBtemplate) boolean para.a = para.b

function typelist seq.mytype
[
 typeint
 , typeboolean
 , typereal
 , typeptr
 , typebyte
 , typepacked2
 , typepacked3
 , typepacked4
 , typepacked5
 , typepacked6
]

function hash(a:idxNBtemplate) int findindex(typelist, para.a)

function SeqTypeEq(offset:int) match5
match5(
 symbol(internalmod, "SeqTypeEq", [typeint], typeboolean)
 , 3
 , LOAD(r.1, ibcsub.1, i64)
 + CMP2(r.2, r.1, C64.offset, 32)
 + CAST(r.3, r.2, i64, zext)
 , "TEMPLATE" sub 1
 , 1
 , [i64]
)

function packedSeq(size:int) match5
if size = 1 then
 match5(
  symbol(internalmod, "packedindex", [seqof.typebyte, typeint], typeint)
  , 9
  , BINOP(r.1, ibcsub.2, C64.1, sub)
  + BINOP(r.2, r.1, C64.3, lshr)
  + BINOP(r.3, r.2, C64.2, add)
  + GEP(r.4, i64, ibcsub.1, r.3)
  + LOAD(r.5, r.4, i64)
  + BINOP(r.6, r.1, C64.7, and)
  + BINOP(r.7, r.6, C64.3, shl)
  + BINOP(r.8, r.5, r.7, lshr)
  + BINOP(r.9, r.8, C64.255, and)
  , "TEMPLATE" sub 1
  , 2
  , [i64]
 )
else
 match5(
  symbol(internalmod, "packedSeq", [typeint], typeptr)
  , 3
  , BINOP(r.1, ibcsub.2, C64.size, mul)
  + BINOP(r.2, r.1, C64(2 - size), add)
  + GEP(r.3, i64, ibcsub.1, r.2)
  , "TEMPLATE" sub 1
  , 2
  , [i64]
 )

Function idxNBtemplate(para0:mytype) idxNBtemplate
let para = if para0 ∈ [typeword] then typeint else para0
let f = findencode.idxNBtemplate(para, empty:seq.match5, 0),
if not.isempty.f then f sub 1
else
 let jjj = findindex(typelist, para)
 assert jjj ≤ n.typelist report "GGG1:(jjj):(para)"
 let seqtype = seqof(if jjj ∈ [2, 5] then typeint else para)
 let tlist =
  if jjj < 5 then [SeqTypeEq.0, IdxSeq.para, Callidx.para]
  else [SeqTypeEq.0, IdxSeq.para, SeqTypeEq.1, packedSeq(jjj - 4), Callidx.para]
 for regcount = if jjj < 5 then 2 else 3, e ∈ tlist do regcount + length.e
 let new = idxNBtemplate(para, tlist, regcount),
 let discard = encode.new,
 new

function Callidx(para:mytype) match5
let vv =
 if para = typereal then double
 else if para ∈ [typeint, typeboolean, typebyte] then i64
 else ptr.i64,
match5(
 symbol(internalmod, "callidx", [seqof.para, typeint], para)
 , 4
 , GEP(r.1, i64, ibcsub.1, C64.0)
 + LOAD(r.2, r.1, i64)
 + CAST(r.3, r.2, ptr.function.[vv, i64, ptr.i64, i64], inttoptr)
 + CALL(
  r.4
  , 0
  , 32768
  , function.[vv, i64, ptr.i64, i64]
  , r.3
  , slot.ibcfirstpara2
  , ibcsub.1
  , ibcsub.2
 )
 , "TEMPLATE" sub 1
 , 2
 , [vv]
)

function IdxSeq(para:mytype) match5
let sym = symbol(internalmod, "idxseq", [seqof.para, typeint], typeint),
if para ∈ [typeint, typeboolean, typebyte] then
 match5(
  sym
  , 3
  , BINOP(r.1, ibcsub.2, C64.1, add)
  + GEP(r.2, i64, ibcsub.1, r.1)
  + LOAD(r.3, r.2, i64)
  , "TEMPLATE" sub 1
  , 2
  , [i64]
 )
else if para = typereal then
 match5(
  sym
  , 4
  , BINOP(r.1, ibcsub.2, C64.1, add)
  + GEP(r.2, i64, ibcsub.1, r.1)
  + LOAD(r.3, r.2, i64)
  + CAST(r.4, r.3, double, bitcast)
  , "TEMPLATE" sub 1
  , 2
  , [double]
 )
else
 match5(
  sym
  , 4
  , BINOP(r.1, ibcsub.2, C64.1, add)
  + GEP(r.2, i64, ibcsub.1, r.1)
  + LOAD(r.3, r.2, i64)
  + CAST(r.4, r.3, ptr.i64, inttoptr)
  , "TEMPLATE" sub 1
  , 2
  , [ptr.i64]
 )
 