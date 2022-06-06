Module wasm2

use UTF8

use bits

use funcidx

use standard

use symbol2

use wasm

use words

use seq.byte

use seq.int

use set.int

use seq.mytype

use seq.symbol

use set.symbol

use seq.wfunc

use otherseq.word

use seq.wtype

use stack.wtype

use seq.seq.byte

use stack.seq.byte

use seq.set.symbol

use seq.seq.seq.byte

use process.seq.seq.word

Function print(a:seq.byte)seq.word for acc = "bytes:", @e ∈ a do acc + print.@e /for(acc)

Function allocatesym symbol symbol(moduleref."? core32", "allocate", typeint, typeptr)

Function recordsym(alltypes:typedict, sym:symbol)symbol
for acc = empty:seq.mytype, typ ∈ paratypes.sym do
 let kind = basetype(typ, alltypes)
 acc + if kind = typeboolean ∨ kind = typereal then kind else typeint
/for(symbol(moduleref."$$record", "$$record", acc, typeint))

Function initwordsbody seq.byte
assert encodingbase + noencodings * 4 < globalspace report"globalspace not big enough"
let charseq = seqof.typeref."char standard stdlib"
let symboladdword = 
 symbol(moduleref("stdlib encoding", charseq)
 , "addencoding"
 , [addabstract(typeref."encodingstate encoding stdlib", charseq), charseq]
 , addabstract(typeref."encodingstate encoding stdlib", charseq)
 )
for l = Wlocal.1, loc ∈ initialwordlocations do l + const64.loc + Wcall.symboladdword /for(funcbody([i32, i64]
, switchcontext.newcontext2.0 + const64.1
+ Wcall.symbol(internalmod, "getinstance", typeint, typeint)
+ Wdefine.1
+ store(load(getencodingaddress.const64.1, 0), l + i32wrapi64, 0)
+ store(load(getencodingaddress.const64.2, 0)
, const64.2 + Wcall.symbol(internalmod, "getinstance", typeint, typeint) + i32wrapi64
, 0
)
+ switchcontext.newcontext2.0
))

function getencodingaddress(encodingno:seq.byte)seq.byte
{@currentprocess+encodingbase+4*encodingno}Gcurrentprocess + encodingno + const64.4 + i64mul
+ i32wrapi64
+ const32.encodingbase
+ i32add
+ i32add

Function getinstancefunc(alltypes:typedict)int
let Emptyseq = Constant2.[Lit.0, Lit.0, Record.[typeint, typeint]]
let empty4 = const64.getoffset.Constant2.[Emptyseq, Emptyseq, Emptyseq, Emptyseq, Sequence(seqof.typeint, 4)]
let emptyinstance = 
 Wlocal.0 + const64.0 + empty4 + empty4 + const64.getoffset.Emptyseq + Wlocal.0
 + Wcall.recordsym(alltypes
 , symbol(internalmod
 , "record"
 , [typeint, typeint, typeint, typeint, typeint, typeint]
 , typeptr
 )
 )
 + i32wrapi64
let addr = getencodingaddress.Wlocal.0
addf(alltypes
, symbol(internalmod, "getinstance", typeint, typeint)
, funcbody([i64, i64, i32, i32]
, load(addr, 0) + const32.0 + i32eq
+ Wif(i32
, store(addr, const64.1 + Wcall.allocatesym, 0) + emptyinstance + Wdefine.3
+ store(load(addr, 0), Wlocal.3, 0)
+ {store currentprocess in encodinginfo}store(load(addr, 0), Gcurrentprocess, 4)
+ Wlocal.3
, load(load(addr, 0), 0)
)
+ i64extendi32u
)
)

Function exportreclaimspace(alltypes:typedict)seq.byte
let sym = symbol(internalmod, "reclaimspace", typereal)
let discard = 
 addf(alltypes
 , sym
 , funcbody([i32]
 , store(Gcurrentprocess, Gfreeblocks, 0)
 + setGlobal(freeblocks
 , Glastfree + const32.toint.{will produce 32bit constant 0xFFFF0000}0xFFFFFFFFFFFF0000 + i32and
 )
 + switchcontext.load(Gcurrentprocess, parentprocess)
 + switchcontext.newcontext2.0
 + const64.0
 + f64converti64s
 )
 )
exportfunc(funcidx.sym, wordname.sym)

Function exportprocessbody(alltypes:typedict)seq.byte
let sym = symbol(internalmod, "processbody", typereal, typereal, typereal)
let funccall = 
 Wlocal.0 + i64truncf64s + Wlocal.1 + i32truncf64s + Wcallindirect.typeindex([i64], i64) + Wdefine.4
let discard = 
 addf(alltypes
 , sym
 , funcbody([i32, i32, i64, i32]
 , switchcontext.newcontext2.2 + funccall + Gcurrentprocess + Wdefine.5
 + switchcontext.load(Gcurrentprocess, parentprocess)
 + Wlocal.0
 + i32truncf64u
 + i32load
 + tobyte.2
 + tobyte.0
 + localtee
 + LEBu.2
 + const32.0
 + i32gtu
 + Wif(void, Wlocal.4 + Wlocal.2 + Wcallindirect.typeindex([i64], i64) + Wdefine.4)
 + {reclaim space}store(Wlocal.5, Gfreeblocks, 0)
 + setGlobal(freeblocks
 , load(Wlocal.5, lastfree)
 + const32.toint.{will produce 32bit constant 0xFFFF0000}0xFFFFFFFFFFFF0000
 + i32and
 )
 + {create process record}const64.0
 + const64.0
 + Wlocal.4
 + (const64.0 + const64.1 + Wlocal.4
 + Wcall.recordsym(alltypes, symbol(internalmod, "record", [typeint, typeint, typeint], typeptr)))
 + Wcall.recordsym(alltypes
 , symbol(internalmod, "record", [typeint, typeint, typeint, typeptr], typeptr)
 )
 + f64converti64s
 )
 )
exportfunc(funcidx.sym, wordname.sym)

Function exporthandleerror(alltypes:typedict)seq.byte
let sym = symbol(internalmod, "handleerror", typereal, typereal)
let discard = 
 addf(alltypes
 , sym
 , funcbody([i32, i64]
 , Wlocal.0 + i64truncf64s + Wdefine.2 + Wlocal.2 + const64.0 + i64les
 + Wif(void, const64.getoffset.wordsconst."other error" + Wdefine.2)
 + switchcontext.load(Gcurrentprocess, parentprocess)
 + Wlocal.2
 + Wcall.symbol4(moduleref("webassembly seq", typeword)
 , "type"_1
 , seqof.typeword
 , [seqof.typeword]
 , seqof.typeword
 )
 + Wdefine.2
 + {create process record}const64.1
 + Wlocal.2
 + const64.0
 + Wcall.recordsym(alltypes, symbol(internalmod, "record", [typeint, typeint, typeint], typeptr))
 + f64converti64s
 )
 )
exportfunc(funcidx.sym, wordname.sym)

function newcontext2(newprocess:int)seq.byte
{"this"is tmp to store current process.  /br Update values of nextfree and last free in current process record.  /br Get 
new memory segment which sets global nextfree and global lastfree  /br create new process context record and place in currentprocess  /br 
set parentprocess in new context record  /br set up encodings in new context record}
getspace.false
+ Gnextfree
+ const32.8
+ i32sub
+ Wdefine.newprocess
+ store(Wlocal.newprocess, Gcurrentprocess, parentprocess)
+ for acc = empty:seq.byte, i ∈ arithseq(noencodings, 4, 0)do
 acc + store(Wlocal.newprocess, load(Gcurrentprocess, encodingbase + i), encodingbase + i)
/for(acc)
+ store(Wlocal.newprocess, Wlocal.newprocess + const32.contextsize + i32add, nextfree)
+ store(Wlocal.newprocess, Glastfree, lastfree)
+ store(Wlocal.newprocess, const32.0, 0)
+ Wlocal.newprocess

function switchcontext(p:seq.byte)seq.byte
store(Gcurrentprocess, Gnextfree, nextfree) + store(Gcurrentprocess, Glastfree, lastfree)
+ setGlobal(currentprocess, p)
+ setGlobal(nextfree, load(Gcurrentprocess, nextfree))
+ setGlobal(lastfree, load(Gcurrentprocess, lastfree))

Function addencodingfunc(alltypes:typedict)int
let encodingpair = 1
let addfunc = 2
let deepcopyfunc = 3
let pairaddress = 4
let instance = 5
let owningprocess = 6
let callingprocess = 7
addf(alltypes
, symbol(internalmod, "addencoding", [typeint, typeptr, typeint, typeint], typeint)
, {parameters encodingnumber, encodingpair, add2, deepcopy}
funcbody([i32, i64, i32, i32]
, Wlocal.0 + Wcall.symbol(internalmod, "getinstance", typeint, typeint) + Wdefine.instance
+ Gcurrentprocess
+ Wdefine.callingprocess
+ load(getencodingaddress.Wlocal.0, 0)
+ Wdefine.pairaddress
+ load(Wlocal.pairaddress, 4)
+ Wdefine.owningprocess
+ Wlocal.owningprocess
+ Wlocal.callingprocess
+ i32eq
+ Wif(i64
, Wlocal.instance + Wlocal.encodingpair
+ ({why does encodingpair need deepcopy ? when owningprocess=currentprocess?}Wlocal.deepcopyfunc
+ i32wrapi64
+ Wcallindirect.typeindex([i64], i64))
+ Wlocal.addfunc
+ i32wrapi64
+ Wcallindirect.typeindex([i64, i64], i64)
, {change so space is allocate from owningprocess}switchcontext.Wlocal.owningprocess
+ {call code to add encoding}Wlocal.instance
+ (Wlocal.encodingpair + Wlocal.deepcopyfunc + i32wrapi64 + Wcallindirect.typeindex([i64], i64))
+ Wlocal.addfunc
+ i32wrapi64
+ Wcallindirect.typeindex([i64, i64], i64)
+ {change back so space in allocated in orignal process}switchcontext.Wlocal.callingprocess
)
+ Wdefine.instance
+ {store modified instance}store(Wlocal.pairaddress, Wlocal.instance + i32wrapi64, 0)
+ {get last added}Wlocal.instance
+ i32wrapi64
+ i64load
+ tobyte.3
+ tobyte.40
+ return
)
)

Function nextfree int 4

Function lastfree int 8

function currentprocess int 12

function parentprocess int 12

function freeblocks int 16

function encodingbase int 16

function noencodings int 40

function contextsize int noencodings * 2 + encodingbase / 2

function getspace(link:boolean)seq.byte
Gfreeblocks + const32.0 + i32eq
+ Wif(void
, setGlobal(nextfree, const32.1 + [memorygrow, tobyte.0] + const32.2^16 + i32mul)
, setGlobal(nextfree, Gfreeblocks) + setGlobal(freeblocks, load(Gfreeblocks, 0)) + Gnextfree
+ i64extendi32u
+ const64.8192
+ Wcall.symbol(moduleref."webassembly inputoutput", "set2zero", typeptr, typeint, typeptr)
+ drop
)
+ if link then
 {link up allocated blocks}
 store(Gnextfree
 , Glastfree + const32.toint.{will produce 32bit constant 0xFFFF0000}0xFFFFFFFFFFFF0000 + i32and
 , 0
 )
else empty:seq.byte /if
+ setGlobal(nextfree, Gnextfree + const32.8 + i32add)
+ setGlobal(lastfree, Gnextfree + const32(8180 * 8) + i32add)

Function allocatefunc(alltypes:typedict)int
addf(alltypes
, allocatesym
, funcbody([i32, i32]
, Gnextfree + Wdefine.1 + Wlocal.1 + Wlocal.0 + i32wrapi64 + const32.8 + i32mul + i32add + Wdefine.2
+ Wlocal.2
+ Glastfree
+ i32gtu
+ Wif(void
, getspace.true + Gnextfree + Wdefine.1 + Wlocal.1 + Wlocal.0 + i32wrapi64 + const32.8 + i32mul + i32add
+ Wdefine.2
+ setGlobal(nextfree, Wlocal.2)
, setGlobal(nextfree, Wlocal.2)
)
+ {Wlocal.1+i64extendi32u+Wlocal.0+Wcall.symbol(moduleref."webassembly inputoutput", "set2zero", typeptr, typeint 
, typeptr)+drop+}
Wlocal.1
+ return
)
)

function setGlobal(offset:int, val:seq.byte)seq.byte store(const32.0, val, offset)

function Gfreeblocks seq.byte load(const32.0, freeblocks)

function Gnextfree seq.byte load(const32.0, nextfree)

function Glastfree seq.byte load(const32.0, lastfree)

function Gcurrentprocess seq.byte load(const32.0, currentprocess)

function load(base:seq.byte, offset:int)seq.byte base + i32load + tobyte.2 + LEBu.offset

function store(base:seq.byte, arg:seq.byte, i:int)seq.byte base + arg + i32store + tobyte.2 + LEBu.i

Function Wif(type:wtype, thenclause:seq.byte)seq.byte Wif(type, thenclause, empty:seq.byte)

Function Wif(type:wtype, thenclause:seq.byte, elseclause:seq.byte)seq.byte
[tobyte.0x04] + first.asbytes.type + thenclause
+ if isempty.elseclause then empty:seq.byte else[tobyte.0x05] + elseclause /if
+ END

Function const64(i:int)seq.byte[i64const] + LEBs.i

Function const32(i:int)seq.byte[i32const] + LEBs.i

Function Wlocal(i:int)seq.byte[localget] + LEBu.i

Function Wdefine(local:int)seq.byte[localset] + LEBu.local

Function Wcallindirect(typeindex:int)seq.byte[callindirect] + LEBu.typeindex + tobyte.0 