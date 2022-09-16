Module knownWfunc

use bits

use funcidx

use standard

use symbol2

use wasm

use wasm2

use seq.byte

use seq.wfunc

Function abortfunc symbol symbol(moduleref."* core", "abortfunc", typereal, typereal)

Function callprocessfunc symbol symbol(internalmod, "callprocess", typereal, typereal, typereal)

Function knownWfunc(alltypes:typedict,typestack:mytype)seq.wfunc
[wfunc(alltypes, symbol(internalmod, "not", typeboolean, typeboolean), const32.1 + i32xor)
, wfunc(alltypes
, symbol(internalmod, "getseqlength", typeptr, typeint)
, [i32wrapi64, i64load, tobyte.3] + LEBu.8
)
, wfunc(alltypes
, symbol(internalmod, "getseqtype", typeptr, typeint)
, [i32wrapi64, i64load, tobyte.3] + LEBu.0
)
, wfunc(alltypes
, symbol(internalmod
, "stackcall"
, typestack
, typeint
, typestack
)
, [i32wrapi64] + Wcallindirect.typeindex([i64], i64)
)
, wfunc(alltypes
, symbol(internalmod
, "stackcall2"
, typestack
, typeint
, typeint
, typestack
)
, [i32wrapi64] + Wcallindirect.typeindex([i64, i64], i64)
)
, wfunc(alltypes
, symbol(internalmod, "loadvalue", typeint, typeint)
, [i32wrapi64, i64load, tobyte.3, tobyte.0]
)
, wfunc(alltypes
, symbol(internalmod, "packedindex", seqof.typebyte, typeint, typeptr)
, [i64add, i32wrapi64, i64load8u, tobyte.0] + LEBu.15
)
, wfunc(alltypes
, symbol(internalmod, "packedindex", typepackedseq2, typeint, typeptr)
, const64(2 * 8) + i64mul + const64(8 * (2 - 2)) + i64sub + i64add
)
, wfunc(alltypes
, symbol(internalmod, "packedindex", typepackedseq3, typeint, typeptr)
, const64(3 * 8) + i64mul + const64(8 * (3 - 2)) + i64sub + i64add
)
, wfunc(alltypes
, symbol(internalmod, "packedindex", typepackedseq4, typeint, typeptr)
, const64(4 * 8) + i64mul + const64(8 * (4 - 2)) + i64sub + i64add
)
, wfunc(alltypes
, symbol(internalmod, "packedindex", typepackedseq5, typeint, typeptr)
, const64(5 * 8) + i64mul + const64(8 * (5 - 2)) + i64sub + i64add
)
, wfunc(alltypes
, symbol(internalmod, "packedindex", typepackedseq6, typeint, typeptr)
, const64(6 * 8) + i64mul + const64(8 * (6 - 2)) + i64sub + i64add
)
, wfunc(alltypes, symbol(internalmod, "bitcast", typeint, typeptr), empty:seq.byte)
, wfunc(alltypes, symbol(internalmod, "toint", typebyte, typeint), empty:seq.byte)
, wfunc(alltypes, symbol(internalmod, "bitcast", typeptr, typeptr), empty:seq.byte)
, wfunc(alltypes, symbol(internalmod, "bitcast", seqof.typeint, typeptr), empty:seq.byte)
, wfunc(alltypes, symbol(internalmod, "toreal", typeint, typereal), [f64converti64s])
, wfunc(alltypes
, symbol(internalmod, "bits2real", seqof.typebits, typereal)
, [f64converti64s]
)
, wfunc(alltypes
, symbol(internalmod, "real2bytes", typereal, seqof.typebits)
, [i64truncf64s]
)
, wfunc(alltypes
, symbol(internalmod, "representation", typereal, typeint)
, [i64reinterpretf64]
)
, wfunc(alltypes
, symbol(internalmod, "casttoreal", typeint, typereal)
, [f64reinterpreti64]
)
, wfunc(alltypes, symbol(internalmod, "intpart", typereal, typeint), [i64truncf64s])
, wfunc(alltypes, symbol(internalmod, "+", typereal, typereal, typereal), [f64add])
, wfunc(alltypes, symbol(internalmod, "-", typereal, typereal, typereal), [f64sub])
, wfunc(alltypes, symbol(internalmod, "*", typereal, typereal, typereal), [f64mul])
, wfunc(alltypes, symbol(internalmod, "/", typereal, typereal, typereal), [f64div])
, wfunc(alltypes, symbol(internalmod, ">", typeint, typeint, typeboolean), [i64gts])
, wfunc(alltypes, symbol(internalmod, "=", typeint, typeint, typeboolean), [i64eq])
, wfunc(alltypes, symbol(internalmod, "=", typeboolean, typeboolean, typeboolean), [i32eq])
, wfunc(alltypes, symbol(internalmod, "+", typeint, typeint, typeint), [i64add])
, wfunc(alltypes, symbol(internalmod, "-", typeint, typeint, typeint), [i64sub])
, wfunc(alltypes, symbol(internalmod, "*", typeint, typeint, typeint), [i64mul])
, wfunc(alltypes, symbol(internalmod, "/", typeint, typeint, typeint), [i64divs])
, wfunc(alltypes, symbol(internalmod, "<<", typebits, typeint, typebits), [i64shl])
, wfunc(alltypes, symbol(internalmod, ">>", typebits, typeint, typebits), [i64shru])
, wfunc(alltypes, symbol(internalmod, "∧", typebits, typebits, typebits), [i64and])
, wfunc(alltypes, symbol(internalmod, "∨", typebits, typebits, typebits), [i64or])
, wfunc(alltypes, symbol(internalmod, "xor", typebits, typebits, typebits), [i64xor])
, wfunc(alltypes
, symbol(internalmod, "GEP", seqof.typeptr, typeint, typeptr)
, const64.8 + i64mul + i64add
)
, wfunc(alltypes
, symbol(internalmod, "GEP", seqof.typeint, typeint, typeptr)
, const64.8 + i64mul + i64add
)
, wfunc(alltypes
, symbol(internalmod, "processisaborted", typeptr, typeboolean)
, [i32wrapi64, i32load, tobyte.2] + LEBu.0
)
, wfunc(alltypes, abortsymbol.typeint, [f64converti64s] + Wcall.abortfunc + drop + const64.0)
, wfunc(alltypes, abortsymbol.typebyte, [f64converti64s] + Wcall.abortfunc + drop + const64.0)
, wfunc(alltypes, abortsymbol.typeptr, [f64converti64s] + Wcall.abortfunc + drop + const64.0)
, wfunc(alltypes
, abortsymbol.typeref."packed2 tausupport *"
, [f64converti64s] + Wcall.abortfunc + drop + const64.0
)
, wfunc(alltypes
, abortsymbol.typeref."packed3 tausupport *"
, [f64converti64s] + Wcall.abortfunc + drop + const64.0
)
, wfunc(alltypes
, abortsymbol.typeref."packed4 tausupport *"
, [f64converti64s] + Wcall.abortfunc + drop + const64.0
)
, wfunc(alltypes, abortsymbol.typeboolean, [f64converti64s] + Wcall.abortfunc + drop + const32.0)
, wfunc(alltypes, abortsymbol.typereal, [f64converti64s] + Wcall.abortfunc)
, wfunc(alltypes
, symbol4(internalmod, "bitcast"_1, seqof.typeint, [typereal], seqof.typeint)
, [i64reinterpretf64]
)
, wfunc(alltypes
, symbol4(internalmod, "bitcast"_1, seqof.typebyte, [typereal], seqof.typebyte)
, [i64reinterpretf64]
)
, wfunc(alltypes
, symbol4(internalmod, "bitcast"_1, typestack, [typereal], typestack)
, [i64reinterpretf64]
)
, wfunc(alltypes
, symbol(builtinmod.typeptr, "fld", [typeptr, typeint], typeptr)
, const64.8 + i64mul + i64add + i32wrapi64 + [i64load] + tobyte.3 + LEBu.0
)
, wfunc(alltypes
, symbol(builtinmod.typeint, "fld", [typeptr, typeint], typeint)
, const64.8 + i64mul + i64add + i32wrapi64 + [i64load] + tobyte.3 + LEBu.0
)
, wfunc(alltypes
, symbol(builtinmod.typereal, "fld", [typeptr, typeint], typereal)
, const64.8 + i64mul + i64add + i32wrapi64 + [f64load] + tobyte.3 + LEBu.0
)
, wfunc(alltypes
, symbol(builtinmod.typeboolean, "fld", [typeptr, typeint], typeboolean)
, const64.8 + i64mul + i64add + i32wrapi64 + [i32load] + tobyte.2 + LEBu.0
)
, wfunc(alltypes
, symbol(builtinmod.typeref."packed3 tausupport *"
, "fld"
, [typeptr, typeint]
, typeref."packed3 tausupport *"
)
, const64.24 + i64mul + i64add + i32wrapi64 + [f64load] + tobyte.3 + LEBu.0
)
, wfunc(alltypes
, symbol(builtinmod.typeref."packed4 tausupport *"
, "fld"
, [typeptr, typeint]
, typeref."packed4 tausupport *"
)
, const64.32 + i64mul + i64add + i32wrapi64 + [f64load] + tobyte.3 + LEBu.0
)
, wfunc(alltypes
, symbol(internalmod, "idxseq", seqof.typeptr, typeint, typeptr)
, const64.8 + [i64mul, i64add, i32wrapi64, i64load, tobyte.3] + LEBu.8
)
, wfunc(alltypes
, symbol(internalmod, "idxseq", seqof.typeint, typeint, typeint)
, const64.8 + [i64mul, i64add, i32wrapi64, i64load, tobyte.3] + LEBu.8
)
, wfunc(alltypes
, symbol(internalmod, "idxseq", seqof.typebyte, typeint, typeint)
, const64.8 + [i64mul, i64add, i32wrapi64, i64load, tobyte.3] + LEBu.8
)
, wfunc(alltypes
, symbol(internalmod, "idxseq", typepackedseq2, typeint, typeptr)
, const64.8 + [i64mul, i64add, i32wrapi64, i64load, tobyte.3] + LEBu.8
)
, wfunc(alltypes
, symbol(internalmod, "idxseq", typepackedseq3, typeint, typeptr)
, const64.8 + [i64mul, i64add, i32wrapi64, i64load, tobyte.3] + LEBu.8
)
, wfunc(alltypes
, symbol(internalmod, "idxseq", typepackedseq4, typeint, typeptr)
, const64.8 + [i64mul, i64add, i32wrapi64, i64load, tobyte.3] + LEBu.8
)
, wfunc(alltypes
, symbol(internalmod, "idxseq", typepackedseq5, typeint, typeptr)
, const64.8 + [i64mul, i64add, i32wrapi64, i64load, tobyte.3] + LEBu.8
)
, wfunc(alltypes
, symbol(internalmod, "idxseq", typepackedseq6, typeint, typeptr)
, const64.8 + [i64mul, i64add, i32wrapi64, i64load, tobyte.3] + LEBu.8
)
, wfunc(alltypes
, symbol(internalmod, "idxseq", seqof.typeboolean, typeint, typeboolean)
, const64.8 + [i64mul, i64add, i32wrapi64, i64load, tobyte.3] + LEBu.8 + i32wrapi64
)
, wfunc(alltypes
, symbol(internalmod, "idxseq", seqof.typereal, typeint, typereal)
, const64.8 + [i64mul, i64add, i32wrapi64, f64load, tobyte.3] + LEBu.8
)
, wfunc(alltypes
, symbol(internalmod, "stacktrace", seqof.typeword)
, const64.getoffset.wordsconst.""
)
, wfunc(alltypes
, symbol(internalmod, "loadedLibs", seqof.typeword)
, const64.getoffset.wordsconst.""
)
]

function typepackedseq2 mytype seqof.typeref."packed2 tausupport *"

function typepackedseq3 mytype seqof.typeref."packed3 tausupport *"

function typepackedseq4 mytype seqof.typeref."packed4 tausupport *"

function typepackedseq5 mytype seqof.typeref."packed5 tausupport *"

function typepackedseq6 mytype seqof.typeref."packed6 tausupport *" 