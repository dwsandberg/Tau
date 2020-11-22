Module codetemplates


use seq.bit

use bits

use fileio

use seq.seq.int

use seq.int

use set.int

use internalbc

use llvm

use llvmconstants

use otherseq.llvmtype

use seq.llvmtype

use mangle

use encoding.match5

use seq.match5

use seq.mytype

use persistant

use stdlib

use seq.seq.symbol

use seq.symbol

use set.symbol

use symbol

use seq.templatepart

use textio

Export constdata seq.slot

Export wordref(w:word)int

Export addliblib(libname:seq.word, mods:int, profiledata:int)int

Function mangledname(s:symbol)word mangle(fsig.s, module.s)

Function isexternal(s:symbol) boolean
   isbuiltin.module.s &and (fsig.s)_1 in "sqrt sin cos tan arcsin arccos loadedlibs" 

Function tollvmtype(alltypes:typedict, s:symbol)llvmtype
 if fsig.s = "option(T, word seq)"then function.constantseq(nopara.s + 2, i64)
 else 
 let starttypes=if isexternal.s   then [ tollvmtype(alltypes, resulttype.s)] else [ tollvmtype(alltypes, resulttype.s), i64]
 function.@(+, tollvmtype.alltypes,starttypes
 , paratypes.s)

function tollvmtype(alltypes:typedict, s:mytype)llvmtype
 let kind = kind.gettypeinfo(alltypes, s)
  if kind = "int"_1 then i64 else if kind = "real"_1 then double else ptr.i64

Function conststype llvmtype array(-2, i64)

Function profiletype llvmtype array(-3, i64)

Export type:match5

Export length(match5)int // no of instruction that return results //

Export action(match5)word

Export arg(match5)int

type match5 is record sym:symbol, length:int, parts:seq.templatepart, action:word, arg:int, code:seq.symbol, functype:llvmtype
 
function match5(sym:symbol, length:int, parts:seq.templatepart, action:word, arg:slot)match5
match5(sym, length, parts, action, toint.arg, empty:seq.symbol, i64)

function match5(sym:symbol, length:int, b:internalbc)match5
 match5(sym, length, getparts.b,"TEMPLATE"_1, slot.nopara.sym)

Export code(match5)seq.symbol

Export functype(match5)llvmtype

Export type:symbol

Function  parametertypes(m:match5)seq.word 
// used for records and loopblock //
fsig.sym.m+module.sym.m

Export type:program

Function_(m:seq.match5, d:symbol)match5
 let e = findencode.match5(d, 0, empty:seq.templatepart,"NOTFOUND"_1, slot.0)
  assert not.isempty.e report"LL" + fsig.d + module.d
    e_1

function =(a:match5, b:match5)boolean   sym.a=sym.b

function hash(a:match5)int   fsighash.sym.a

function assignencoding(l:int, a:match5)int l + 1

Function options(match5map:seq.match5, m:match5)seq.word options.code.m

function table seq.match5
let t = [ match5(symbol("bitcast(int seq seq)","builtin","int seq"), 0, emptyinternalbc)
, match5(symbol("bitcast(ptr)","builtin","int"), 1, CAST(r.1, slot.ibcsub1, i64, ptrtoint))
, match5(symbol("bitcast(int seq)","builtin","int"), 1, CAST(r.1, slot.ibcsub1, i64, ptrtoint))
, match5(symbol("bitcast(int)","builtin","int seq"), 1, CAST(r.1, slot.ibcsub1, ptr.i64, inttoptr))
, match5(symbol("isnull(ptr)","builtin","boolean"), 3, CAST(r.1, slot.ibcsub1, i64, ptrtoint) + CMP2(r.2, r.1, C64.0, 32)
+ CAST(r.3, r.2, i64, zext))
, match5(symbol("nullptr","builtin","ptr"), 1, CAST(r.1, C64.0, ptr.i64, inttoptr))
, match5(symbol("IDX(int seq,int)","builtin","int"), 2, GEP(r.1, i64, slot.ibcsub1, slot.ibcsub2) + LOAD(r.2, r.1, i64))
, match5(symbol("IDX(int seq seq,int)","builtin","int seq "), 3, GEP(r.1, i64, slot.ibcsub1, slot.ibcsub2) + LOAD(r.2, r.1, i64)
+ CAST(r.3, r.2, ptr.i64, inttoptr))
, match5(symbol("IDX(ptr seq,int)","builtin","ptr"), 3, GEP(r.1, i64, slot.ibcsub1, slot.ibcsub2) + LOAD(r.2, r.1, i64)
+ CAST(r.3, r.2, ptr.i64, inttoptr))
, match5(symbol("IDX(real seq,int)","builtin","real"), 3, GEP(r.1, i64, slot.ibcsub1, slot.ibcsub2) + LOAD(r.2, r.1, i64)
+ CAST(r.3, r.2, double, bitcast))
  , // match5(1,"getseqtypeZbuiltinZTzseq"_1, 1, LOAD(r.1, slot.ibcsub1, i64))  
, // match5(symbol("STKRECORD(ptr,ptr)","builtin","ptr"), 3, ALLOCA(r.1, ptr.ptr.i64, i64, C64.2, 0) + STORE(r.2, r.1, slot.ibcsub1)
+ GEP(r.2, ptr.i64, r.1, C64.1)
+ STORE(r.3, r.2, slot.ibcsub2)
+ GEP(r.3, ptr.i64, r.1, C64.0))
, match5(symbol("intpart(real)","builtin","real"), 1, CAST(r.1, slot.ibcsub1, i64, fptosi))
, match5(symbol("toreal(int)","builtin","real"), 1, CAST(r.1, slot.ibcsub1, double, sitofp))
, match5(symbol("-(real,real)","builtin","real"), 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, sub))
, match5(symbol("+(real,real)","builtin","real"), 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, add))
, match5(symbol("*(real,real)","builtin","real"), 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, mul))
, match5(symbol("/(real,real)","builtin","real"), 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, sdiv))
, match5(symbol("casttoreal(int)","builtin","real"), 1, CAST(r.1, slot.ibcsub1, double, bitcast))
, match5(symbol("representation(real)","builtin","int"),  1, CAST(r.1, slot.ibcsub1, i64, bitcast))
, match5(symbol("?(real,real)","builtin","ordering"), 5, CMP2(r.1, slot.ibcsub1, slot.ibcsub2, 3) + CAST(r.2, r.1, i64, zext)
+ CMP2(r.3, slot.ibcsub1, slot.ibcsub2, 2)
+ CAST(r.4, r.3, i64, zext)
+ BINOP(r.5, r.2, r.4, add))
, match5(symbol("?(int,int)","builtin","ordering"), 5, CMP2(r.1, slot.ibcsub1, slot.ibcsub2, 39) + CAST(r.2, r.1, i64, zext)
+ CMP2(r.3, slot.ibcsub1, slot.ibcsub2, 38)
+ CAST(r.4, r.3, i64, zext)
+ BINOP(r.5, r.2, r.4, add))
, match5(symbol("cast(T seq, int, int)","builtin","ptr"), 1, GEP(r.1, i64, slot.ibcsub1, slot.ibcsub2))
, match5(symbol(">(int,int)","builtin","boolean"), 2, CMP2(r.1, slot.ibcsub1, slot.ibcsub2, 38) + CAST(r.2, r.1, i64, zext))
, match5(symbol("not(boolean)","builtin","boolean"), 1, BINOP(r.1, slot.ibcsub1, C64.1, xor))
, // include aborted here so does not show up in profile results match5("abortedZbuiltinZTzprocess"_1, 1, CALL(1, 0, 32768, typ.function.[ i64, i64, i64], C."abortedZbuiltinZTzprocess",-1, ibcsub1)), Including this as a template causes subtle compile errors //
  match5(symbol("=(int,int)","builtin","boolean"), 2, CMP2(r.1, slot.ibcsub1, slot.ibcsub2, 32) + CAST(r.2, r.1, i64, zext))
, match5(symbol("-(int,int)","builtin","int"), 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, sub))
, match5( symbol("+(int,int)","builtin","int"),1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, add))
, match5(symbol("*(int,int)","builtin","int"), 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, mul))
, match5(symbol("/(int,int)","builtin","int"), 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, sdiv))
, match5(symbol("<<(bits,int)","builtin","bits"), 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, shl))
, match5(symbol(">>(bits,int)","builtin","bits"), 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, lshr))
, match5(symbol("∧(bits,bits)","builtin","bits"), 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, and))
, match5(symbol("∨(bits,bits)","builtin","bits"), 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, or))
, match5(symbol("xor(bits,bits)","builtin","bits"), 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, xor))
, match5(symbol("setfld(int seq,int,int)","builtin","int"), 2, GEP(r.1, i64, slot.ibcsub1, slot.ibcsub2) + STORE(r.2, r.1, slot.ibcsub3)
+ BINOP(r.2, slot.ibcsub2, C64.1, add))]
let discard = @(+, addit, 0, t)
 t


function addit(m:match5)int valueofencoding.encode.m


Function funcdec(alltypes:typedict, i:symbol)int
 toint
 .modulerecord([ mangledname.i], [ toint.FUNCTIONDEC, typ.tollvmtype(alltypes, i), 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])

Function match5map(theprg:program, uses:set.symbol, alltypes:typedict)seq.match5
 let discard3 = table
  buildtemplates(toseq.uses, 1, theprg, empty:seq.symbol, alltypes)

function symboltableentry(name:word)slot symboltableentry(name, i64)

Function symboltableentry(name:word, type:llvmtype)slot symboltableentry([ name], type)

Function symboltableentry(name:seq.word, type:llvmtype)slot
 modulerecord(name, [ toint.FUNCTIONDEC, typ.type, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])

Function global(name:seq.word, type:llvmtype, init:slot)int
 toint.modulerecord(name, [ toint.GLOBALVAR, typ.type, 2, 1 + toint.init, 0, toint.align8 + 1, 0])

function processconstargs(arglist:seq.symbol, i:int, args:seq.int)seq.int
 if i > length.arglist then args
 else
  let xx = arglist_i
  let e = findencode.match5(xx, 0, empty:seq.templatepart,"NOTFOUND"_1, slot.0)
   if isempty.e then empty:seq.int else processconstargs(arglist, i + 1, args + arg.e_1)

function processconst(toprocess:seq.symbol, i:int, notprocessed:seq.symbol)seq.match5
 if i > length.toprocess then
 if isempty.notprocessed then empty:seq.match5 else processconst(notprocessed, 1, empty:seq.symbol)
 else
  let xx = toprocess_i
  let args = processconstargs(constantcode.xx, 1, empty:seq.int)
   if isempty.args then processconst(toprocess, i + 1, notprocessed + toprocess_i)
   else
    let discard = addit.match5(xx, 0, empty:seq.templatepart,"ACTARG"_1, slot.addobject.args)
     processconst(toprocess, i + 1, notprocessed)

function buildtemplates(used:seq.symbol, i:int, theprg:program, const:seq.symbol, alltypes:typedict)seq.match5
 if i > length.used then processconst(const, 1, empty:seq.symbol)
 else
  let xx = used_i
  let pkg = module.xx
   if pkg = "$constant"then buildtemplates(used, i + 1, theprg, const + used_i, alltypes)
   else
    let b = if isbuiltin.pkg then
    findencode.match5(xx, 0, empty:seq.templatepart,"NOTFOUND"_1, slot.0)
    else empty:seq.match5
     if length.b > 0 then buildtemplates(used, i + 1, theprg, const, alltypes)
     else
      let m = if isFref.xx then
      let mn = mangledname.(constantcode.xx)_1
       let functyp = ptr.tollvmtype(alltypes,(constantcode.xx)_1)
        match5(xx, 0, empty:seq.templatepart,"ACTARG"_1, ptrtoint(functyp, symboltableentry(mn, functyp)))
      else if islit.xx then
      match5(xx, 0, empty:seq.templatepart,"ACTARG"_1, if pkg = "$real"then Creal.toint.(fsig.xx)_1 
      else C64.toint.(fsig.xx)_1)
      else if islocal.xx then
      match5(xx, 0, empty:seq.templatepart,"LOCAL"_1, slot.toint.(fsig.xx)_1)
      else if isdefine.xx then
      match5(xx, 0, empty:seq.templatepart,(fsig.xx)_1, slot.toint.(fsig.xx)_2)
      else if isblock.xx then
      let typ = tollvmtype(alltypes, resulttype.xx)
        match5(xx, 0, empty:seq.templatepart,(fsig.xx)_1, nopara.xx, empty:seq.symbol, typ)
      else if isspecial.xx then match5(xx , 0, empty:seq.templatepart,(fsig.xx)_1, slot.nopara.xx)
      else if pkg = "$words"then
      // let ctype = array(length.fsig.xx + 2, i64)let c = DATA(ctype, @(+, wordref, [ 0, length.fsig.xx], fsig.xx))let d = modulerecord("", [ toint.GLOBALVAR, typ.ctype, 2, c + 1, 3, toint.align8 + 1, 0])let f = ptrtoint(ptr.ctype, d)//
       match5(xx, 0, empty:seq.templatepart,"ACTARG"_1, slot.addwordseq2.fsig.xx)
      else if pkg = "$word"then
      match5(xx, 0, empty:seq.templatepart,"ACTARG"_1, slot.wordref.(fsig.xx)_1)
      else if(fsig.xx)_1 = "callidx"_1 ∧ isbuiltin.pkg then
      match5(xx, 0, empty:seq.templatepart,"CALLIDX"_1, 0, empty:seq.symbol, tollvmtype(alltypes, resulttype.xx))
      else if(fsig.xx)_1 = "global"_1 ∧ isbuiltin.pkg then
      match5(xx, 1, GEP(r.1, i64, slot.global([ mangledname.xx], i64, C64.0)))
      else if(fsig.xx)_1 = "blockindexfunc"_1 ∧ isbuiltin.pkg then
      let functype = ptr.function.[ i64, i64, ptr.i64, i64]
        match5(xx, 0, empty:seq.templatepart,"ACTARG"_1, ptrtoint(functype, symboltableentry("indexblocksZassignencodingnumberZintzseqzseqZint"_1, functype)))
      else if isexternal.xx then 
            let symname=  if (fsig.xx)_1  in "arcsin" then "asin"_1 else if (fsig.xx)_1  in "arccos" then "acos"_1
            else  (fsig.xx)_1
            let functype = tollvmtype(alltypes, xx)
       let newcode = CALLSTART(1, 0, 32768, typ.functype, toint.symboltableentry(symname, functype), nopara.xx )
       let code = code.lookupcode(theprg, used_i)
       match5(xx, 1, getparts.newcode,"CALLE"_1, nopara.xx, code, functype)
      else 
       let functype = tollvmtype(alltypes, xx)
       let newcode = CALLSTART(1, 0, 32768, typ.functype, toint.symboltableentry(mangledname.xx, functype), nopara.xx + 1)
       let code = code.lookupcode(theprg, used_i)
       match5(xx, 1, getparts.newcode,"CALL"_1, nopara.xx, code, functype)
      let discard4 = addit.m
       buildtemplates(used, i + 1, theprg, const, alltypes)
       


Function usetemplate(t:match5, deltaoffset:int, argstack:seq.int)internalbc
 let args = if action.t = "CALL"_1 then empty:seq.int
 else subseq(argstack, length.argstack - arg.t + 1, length.argstack)
  processtemplate(parts.t, deltaoffset, args)