Module wasm2

use bits

use seq.byte

use funcidx

use seq.mytype

use standard

use seq.symbol

use symbol2

use wasm

Function %(a:seq.byte) seq.word for acc = "bytes:", @e ∈ a do acc + %.@e, acc

Function allocatesym symbol symbol(moduleref."? core32", "allocate", typeint, typeptr)

Function recordsym(alltypes:typedict, sym:symbol) symbol
for acc = empty:seq.mytype, typ ∈ paratypes.sym
do
 let kind = basetype(typ, alltypes),
 acc + if kind = typeboolean ∨ kind = typereal then kind else typeint,
symbol(moduleref."* $$record", "$$record", acc, typeint)

Function initwordsbody(initprofile:seq.symbol, libname:word) seq.byte
let empty = const32.getoffset("", libname)
let charseq = seqof.typeref."char standard *"
let symboladdwords = symbol(moduleref("* encoding", charseq), "addencodings", seqof.charseq, typeint),
funcbody(
 [i32, i64]
 , store(const32.0, empty, encodings)
  + store(const32.0, empty, thisencoding)
   + switchcontext.newcontext2.0
   + (if isempty.initprofile then empty:seq.byte else Wcall.1#initprofile + drop)
   + const64.getoffset(initialwordconst.libname, libname)
   + Wcall.symboladdwords
   + Wdefine.1
   + switchcontext.newcontext2.0
)

Function reclaimspacefunc(alltypes:typedict) int
addf(
 alltypes
 , symbol(internalmod, "reclaimspace", typereal)
 , funcbody(
  [i32]
  , store(Gcurrentprocess, Gfreeblocks, 0)
   + setGlobal(
    freeblocks
    , Glastfree
     + const32.toint.{will produce 32bit constant 0xFFFF0000} 0xFFFFFFFFFFFF0000
      + i32and
   )
    + switchcontext.load(Gcurrentprocess, parentprocess)
    + switchcontext.newcontext2.0
    + const64.0
    + f64converti64s
 )
)

/ function load (base:seq.byte, offset:int) seq.byte base+i32load+tobyte.2+LEBu.offset

Function processbodyfunc(alltypes:typedict) int
let funccall =
 Wlocal.0
  + i64truncf64s
  + Wlocal.1
  + i32truncf64s
  + Wcallindirect.typeindex([i64], i64)
  + Wdefine.4,
addf(
 alltypes
 , symbol(internalmod, "processbody", typereal, typereal, typereal)
 , funcbody(
  [i32, i32, i64, i32]
  , switchcontext.newcontext2.2
   + funccall
    + Gcurrentprocess
    + Wdefine.5
    + switchcontext.load(Gcurrentprocess, parentprocess)
    + load(Wlocal.0 + i32truncf64u, 0)
    + localtee
    + LEBu.2
    + const32.0
    + i32gtu
    + Wif(void, Wlocal.4 + Wlocal.2 + Wcallindirect.typeindex([i64], i64) + Wdefine.4)
    + {reclaim space} store(Wlocal.5, Gfreeblocks, 0)
    + setGlobal(
    freeblocks
    , load(Wlocal.5, lastfree)
     + const32.toint.{will produce 32bit constant 0xFFFF0000} 0xFFFFFFFFFFFF0000
      + i32and
   )
    + {create process record} const64.0
    + const64.0
    + Wlocal.4
    + (
    const64.0
     + const64.1
     + Wlocal.4
     + Wcall.recordsym(alltypes, symbol(internalmod, "record", [typeint, typeint, typeint], typeptr))
   )
    + Wcall.recordsym(alltypes, symbol(internalmod, "record", [typeint, typeint, typeint, typeptr], typeptr))
    + f64converti64s
 )
)

Function handleerrorfunc(alltypes:typedict, libname:word) int
addf(
 alltypes
 , symbol(internalmod, "handleerror", typereal, typereal)
 , funcbody(
  [i32, i64]
  , Wlocal.0
   + i64truncf64s
    + Wdefine.2
    + Wlocal.2
    + const64.0
    + i64les
    + Wif(void, const64.getoffset("other error", libname) + Wdefine.2)
    + switchcontext.load(Gcurrentprocess, parentprocess)
    + Wlocal.2
    + Wcall.symbol4(moduleref("* seq", typeword), 1#"type", seqof.typeword, [seqof.typeword], seqof.typeword)
    + Wdefine.2
    + {create process record} const64.1
    + Wlocal.2
    + const64.0
    + Wcall.recordsym(alltypes, symbol(internalmod, "record", [typeint, typeint, typeint], typeptr))
    + f64converti64s
 )
)

exportfunc (funcidx.sym, wordname.sym)

function newcontext2(newprocess:int) seq.byte
{newprocess is tmp to store new process. 
/br Update values of nextfree and last free in current process record. 
/br Get new memory segment which sets global nextfree and global lastfree
/br create new process context record and place in currentprocess
/br set parentprocess in new context record
/br set up encodings in new context record}
getspace.false
 + Gnextfree
 + const32.8
 + i32sub
 + Wdefine.newprocess
 + store(Wlocal.newprocess, Gcurrentprocess, parentprocess)
 + store(Wlocal.newprocess, load(Gcurrentprocess, encodings), encodings)
 + store(Wlocal.newprocess, load(Gcurrentprocess, thisencoding), thisencoding)
 + store(Wlocal.newprocess, Wlocal.newprocess + const32.contextsize + i32add, nextfree)
 + store(Wlocal.newprocess, Glastfree, lastfree)
 + store(Wlocal.newprocess, const32.0, 0)
 + Wlocal.newprocess

function switchcontext(p:seq.byte) seq.byte
store(Gcurrentprocess, Gnextfree, nextfree)
 + store(Gcurrentprocess, Glastfree, lastfree)
 + setGlobal(currentprocess, p)
 + setGlobal(nextfree, load(Gcurrentprocess, nextfree))
 + setGlobal(lastfree, load(Gcurrentprocess, lastfree))

Function addcriticalfunc(alltypes:typedict) int
let p1 = 0
let p2 = 1
let runin = 2
let addfunc = 3
let callingprocess = 4
let owningprocess = 5,
addf(
 alltypes
 , symbol(internalmod, "critical", [typeint, typeint, typeptr, typeint], typeptr)
 , funcbody(
  [i32, i32]
  , Gcurrentprocess
   + Wdefine.callingprocess
    + Wlocal.runin
    + i32wrapi64
    + Wdefine.owningprocess
    + switchcontext.Wlocal.owningprocess
    + Wlocal.p1
    + Wlocal.p2
    + Wlocal.addfunc
    + i32wrapi64
    + Wcallindirect.typeindex([i64, i64], i64)
    + switchcontext.Wlocal.callingprocess
    + return
 )
)

Function addencodingfunc(alltypes:typedict) int
let einfo = 0
let data = 1
let addfunc = 2
let owningprocess = 3
let callingprocess = 4
let calladd2 =
 Wlocal.einfo
  + load64(Wlocal.data, 0)
  + Wlocal.addfunc
  + i32wrapi64
  + Wcallindirect.typeindex([i64, i64], i64),
addf(
 alltypes
 , symbol(internalmod, "addencoding5", [typeptr, typeptr, typeint], typeptr)
 , {parameters einfo, data, add2}
  funcbody(
   [i32, i32]
   , load(Wlocal.einfo + i32wrapi64, 16)
    + Wdefine.owningprocess
     + Wlocal.owningprocess
     + Gcurrentprocess
     + Wdefine.callingprocess
     + Wlocal.callingprocess
     + i32eq
     + Wif(
     i64
     , calladd2
     , {change so space is allocate from owningprocess} switchcontext.Wlocal.owningprocess
      + {call code to add encoding} calladd2
       + {change back so space in allocated in orignal process} switchcontext.Wlocal.callingprocess
    )
     + return
  )
)
 + addcriticalfunc.alltypes

/Function addencodingfunc (alltypes:typedict) int let einfo = 0 let data = 1 let addfunc = 2 let owningprocess
= 3 let callingprocess = 4 let calladd2 = Wlocal.einfo+Wlocal.data+Wlocal.addfunc+i32wrapi64+
Wcallindirect.typeindex ([i64, i64], i64) addf (alltypes, symbol (internalmod," addencoding4", [
typeptr, typeint, typeint], typeptr), {parameters einfo, data, add2} funcbody ([i32, i32], load
(Wlocal.einfo+i32wrapi64, 16)+Wdefine.owningprocess+Wlocal.owningprocess+Gcurrentprocess+Wdefine
.callingprocess+Wlocal.callingprocess+i32eq+Wif (i64, calladd2, {change so space is allocate from
owningprocess} switchcontext.Wlocal.owningprocess+{call code to add encoding} calladd2+{change
back so space in allocated in orignal process} switchcontext.Wlocal.callingprocess)+return))

function load64(b:seq.byte, offset:int) seq.byte
b + i32wrapi64 + i64load + tobyte.3 + tobyte.offset

function nextfree int 4

function lastfree int 8

function currentprocess int 12

function freeblocks int 16

function encodings int 40

function thisencoding int 48

function parentprocess int 56

function contextsize int 64

function getspace(link:boolean) seq.byte
Gfreeblocks
 + const32.0
 + i32eq
 + Wif(
 void
 , setGlobal(nextfree, const32.1 + [memorygrow, tobyte.0] + const32.2^16 + i32mul)
 , setGlobal(nextfree, Gfreeblocks)
  + setGlobal(freeblocks, load(Gfreeblocks, 0))
   + Gnextfree
   + i64extendi32u
   + const64.8192
   + Wcall.symbol(moduleref."* webIOtypes", "set2zero", typeptr, typeint, typeptr)
   + drop
)
 + (
 if link then
  {link up allocated blocks}
  store(
   Gnextfree
   , Glastfree
    + const32.toint.{will produce 32bit constant 0xFFFF0000} 0xFFFFFFFFFFFF0000
     + i32and
   , 0
  )
 else empty:seq.byte
)
 + setGlobal(nextfree, Gnextfree + const32.8 + i32add)
 + setGlobal(lastfree, Gnextfree + const32(8180 * 8) + i32add)

Function allocatefunc(alltypes:typedict) int
addf(
 alltypes
 , allocatesym
 , funcbody(
  [i32, i32]
  , Gnextfree
   + Wdefine.1
    + Wlocal.1
    + Wlocal.0
    + i32wrapi64
    + const32.8
    + i32mul
    + i32add
    + Wdefine.2
    + Wlocal.2
    + Glastfree
    + i32gtu
    + Wif(
    void
    , getspace.true
     + Gnextfree
      + Wdefine.1
      + Wlocal.1
      + Wlocal.0
      + i32wrapi64
      + const32.8
      + i32mul
      + i32add
      + Wdefine.2
      + setGlobal(nextfree, Wlocal.2)
    , setGlobal(nextfree, Wlocal.2)
   )
    + Wlocal.1
    + return
 )
)

function setGlobal(offset:int, val:seq.byte) seq.byte store(const32.0, val, offset)

function Gfreeblocks seq.byte load(const32.0, freeblocks)

function Gnextfree seq.byte load(const32.0, nextfree)

function Glastfree seq.byte load(const32.0, lastfree)

Function Gcurrentprocess seq.byte load(const32.0, currentprocess)

function load(base:seq.byte, offset:int) seq.byte
base + i32load + tobyte.2 + LEBu.offset

function store(base:seq.byte, arg:seq.byte, i:int) seq.byte
base + arg + i32store + tobyte.2 + LEBu.i

function i64store(base:seq.byte, arg:seq.byte, i:int) seq.byte
base + arg + i64store + tobyte.3 + LEBu.i

function Wif(type:wtype, thenclause:seq.byte) seq.byte
Wif(type, thenclause, empty:seq.byte)

function Wif(type:wtype, thenclause:seq.byte, elseclause:seq.byte) seq.byte
[tobyte.0x04]
 + 1#asbytes.type
 + thenclause
 + (if isempty.elseclause then empty:seq.byte else [tobyte.0x05] + elseclause)
 + END

Function const64(i:int) seq.byte [i64const] + LEBs.i

Function const32(i:int) seq.byte [i32const] + LEBs.i

Function Wlocal(i:int) seq.byte [localget] + LEBu.i

Function Wdefine(local:int) seq.byte [localset] + LEBu.local

Function Wcallindirect(typeindex:int) seq.byte [callindirect] + LEBu.typeindex + tobyte.0 