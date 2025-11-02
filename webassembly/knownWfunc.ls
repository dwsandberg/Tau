Module knownWfunc

use bits

use seq.byte

use funcidx

use standard

use symbol1

use wasm

use wasm2

Function abortfunc symbol symbol(internalmod, "abortfunc", [typereal], typereal)

Function callprocessfunc symbol
symbol(internalmod, "callprocess", [typereal, typereal], typereal)

Function knownWfunc(alltypes:typedict, libname:word) seq.wfunc
[
 wfunc(alltypes, symbol(internalmod, "spacecount", typeint), const64.0)
 , wfunc(
  alltypes
  , symbol(internalmod, "clock", typeint)
  , Wcall.symbol(internalmod, "clockReal", typereal) + i64truncf64s
 )
 , wfunc(alltypes, symbol(internalmod, "not", [typeboolean], typeboolean), const32.1 + i32xor)
 , wfunc(
  alltypes
  , symbol(internalmod, "getseqlength", [typeptr], typeint)
  , [i32wrapi64, i64load, tobyte.3] + LEBu.8
 )
 , wfunc(
  alltypes
  , symbol(internalmod, "getseqtype", [typeptr], typeint)
  , [i32wrapi64, i64load, tobyte.3] + LEBu.0
 )
 , {wfunc (alltypes, symbol (internalmod," bitcast", typereal, typeptr), empty:seq.byte),}
 wfunc(alltypes, symbol(internalmod, "bitcast", [typeint], typeptr), empty:seq.byte)
 , wfunc(alltypes, symbol(internalmod, "toint", [typebyte], typeint), empty:seq.byte)
 , wfunc(alltypes, symbol(internalmod, "bitcast", [typeptr], typeptr), empty:seq.byte)
 , wfunc(alltypes, symbol(internalmod, "bitcast", [seqof.typeint], typeptr), empty:seq.byte)
 , wfunc(alltypes, symbol(internalmod, "toreal", [typeint], typereal), [f64converti64s])
 , wfunc(alltypes, symbol(internalmod, "intpart", [typereal], typeint), [i64truncf64s])
 , wfunc(alltypes, symbol(internalmod, "representation", [typereal], typeint), [i64reinterpretf64])
 , wfunc(alltypes, symbol(internalmod, "casttoreal", [typeint], typereal), [f64reinterpreti64])
 , wfunc(alltypes, symbol(internalmod, "+", [typereal, typereal], typereal), [f64add])
 , wfunc(alltypes, symbol(internalmod, "-", [typereal, typereal], typereal), [f64sub])
 , wfunc(alltypes, symbol(internalmod, "*", [typereal, typereal], typereal), [f64mul])
 , wfunc(alltypes, symbol(internalmod, "/", [typereal, typereal], typereal), [f64div])
 , wfunc(alltypes, symbol(internalmod, ">", [typeint, typeint], typeboolean), [i64gts])
 , wfunc(alltypes, symbol(internalmod, "=", [typeint, typeint], typeboolean), [i64eq])
 , wfunc(alltypes, symbol(internalmod, "=", [typeboolean, typeboolean], typeboolean), [i32eq])
 , wfunc(alltypes, symbol(internalmod, "+", [typeint, typeint], typeint), [i64add])
 , wfunc(alltypes, symbol(internalmod, "-", [typeint, typeint], typeint), [i64sub])
 , wfunc(alltypes, symbol(internalmod, "*", [typeint, typeint], typeint), [i64mul])
 , wfunc(alltypes, symbol(internalmod, "/", [typeint, typeint], typeint), [i64divs])
 , wfunc(alltypes, symbol(internalmod, "<<", [typebits, typeint], typebits), [i64shl])
 , wfunc(alltypes, symbol(internalmod, ">>", [typebits, typeint], typebits), [i64shru])
 , wfunc(alltypes, symbol(internalmod, "∧", [typebits, typebits], typebits), [i64and])
 , wfunc(alltypes, symbol(internalmod, "∨", [typebits, typebits], typebits), [i64or])
 , wfunc(alltypes, symbol(internalmod, "⊻", [typebits, typebits], typebits), [i64xor])
 , wfunc(
  alltypes
  , symbol(internalmod, "GEP", [seqof.typeptr, typeint], typeptr)
  , const64.8 + i64mul + i64add
 )
 , wfunc(
  alltypes
  , symbol(internalmod, "GEP", [seqof.typeint, typeint], typeptr)
  , const64.8 + i64mul + i64add
 )
 , wfunc(
  alltypes
  , symbol(internalmod, "processisaborted", [typeptr], typeboolean)
  , [i32wrapi64, i32load, tobyte.2] + LEBu.0
 )
 , wfunc(
  alltypes
  , symbol(internalmod, "assert", [seqof.typeword], typeint)
  , [f64converti64s] + Wcall.abortfunc + drop + const64.0
 )
 , wfunc(
  alltypes
  , symbol4(internalmod, "bitcast" sub 1, seqof.typeint, [typereal], seqof.typeint)
  , [i64reinterpretf64]
 )
 , wfunc(
  alltypes
  , symbol4(internalmod, "bitcast" sub 1, seqof.typebyte, [typereal], seqof.typebyte)
  , [i64reinterpretf64]
 )
 , wfunc(
  alltypes
  , symbol(builtinmod.typeptr, "fld", [typeptr, typeint], typeptr)
  , const64.8 + i64mul + i64add + i32wrapi64 + [i64load] + tobyte.3 + LEBu.0
 )
 , wfunc(
  alltypes
  , symbol(builtinmod.typeint, "fld", [typeptr, typeint], typeint)
  , const64.8 + i64mul + i64add + i32wrapi64 + [i64load] + tobyte.3 + LEBu.0
 )
 , wfunc(
  alltypes
  , symbol(builtinmod.typereal, "fld", [typeptr, typeint], typereal)
  , const64.8 + i64mul + i64add + i32wrapi64 + [f64load] + tobyte.3 + LEBu.0
 )
 , wfunc(
  alltypes
  , symbol(builtinmod.typeboolean, "fld", [typeptr, typeint], typeboolean)
  , const64.8 + i64mul + i64add + i32wrapi64 + [i32load] + tobyte.2 + LEBu.0
 )
 , wfunc(
  alltypes
  , symbol(
   builtinmod.typeref."packed3 tausupport *"
   , "fld"
   , [typeptr, typeint]
   , typeref."packed3 tausupport *"
  )
  , const64.24 + i64mul + i64add + i32wrapi64 + [f64load] + tobyte.3 + LEBu.0
 )
 , wfunc(
  alltypes
  , symbol(
   builtinmod.typeref."packed4 tausupport *"
   , "fld"
   , [typeptr, typeint]
   , typeref."packed4 tausupport *"
  )
  , const64.32 + i64mul + i64add + i32wrapi64 + [f64load] + tobyte.3 + LEBu.0
 )
 , wfunc(
  alltypes
  , symbol(internalmod, "stacktrace", seqof.typeword)
  , const64.getoffset("", libname)
 )
 , wfunc(
  alltypes
  , symbol(internalmod, "randomint", [typeint], seqof.typeint)
  , Wcall.symbol(moduleref."* SpecialExports", "randomintimp", [typeint], seqof.typeint)
 )
 , wfunc(alltypes, symbol(internalmod, "currentprocess", typeint), Gcurrentprocess + i64extendi32u)
]

function typepackedseq2 mytype seqof.typeref."packed2 tausupport *"

function typepackedseq3 mytype seqof.typeref."packed3 tausupport *"

function typepackedseq4 mytype seqof.typeref."packed4 tausupport *"

function typepackedseq5 mytype seqof.typeref."packed5 tausupport *"

function typepackedseq6 mytype seqof.typeref."packed6 tausupport *" 
