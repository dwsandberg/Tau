Module codetemplates

use seq.bit

use bits

use fileio

use seq.seq.int

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

use standard

use seq.seq.symbol

use seq.symbol

use set.symbol

use symbol

use seq.templatepart

use textio

Export constdata seq.slot

Export wordref(w:word)int

Export addliblib(libname:seq.word, mods:int, profiledata:int,isbase:boolean)int

Function mangledname(s:symbol)word mangle(fsig.s, module.s)

Function isexternal(s:symbol)boolean
 isbuiltin.module.s
 ∧ not((fsig.s)_1 ∈ "aborted loadlib createlib createlib2  unloadlib allocatespace addencoding createfile getinstance dlsymbol getfile addresstosymbol2 randomint 
 getmachineinfo currenttime callstack initialdict createthread  assert callidx3")

Function tollvmtype(alltypes:typedict, s:symbol)llvmtype
 if fsig.s = "option(T, word seq)"then function.constantseq(nopara.s + 2, i64)
 else
  let starttypes = if isexternal.s then [ tollvmtype(alltypes, resulttype.s)]else [ tollvmtype(alltypes, resulttype.s), i64]
   function(paratypes.s @ +(starttypes, tollvmtype(alltypes, @e)))

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

function addtemplate(sym:symbol, length:int, parts:seq.templatepart, action:word, arg:int, code:seq.symbol, functype:llvmtype)match5
 let m = match5(sym, length, parts, action, arg, code, functype)
 let discard = encode.m
  m

function addtemplate(sym:symbol, length:int, parts:seq.templatepart, action:word, arg:slot)match5
 addtemplate(sym, length, parts, action, toint.arg, empty:seq.symbol, i64)

function addtemplate(sym:symbol, length:int, b:internalbc)match5 addtemplate(sym, length, getparts.b,"TEMPLATE"_1, slot.nopara.sym)

function findtemplate(d:symbol)seq.match5 findencode.match5(d, 0, empty:seq.templatepart,"NOTFOUND"_1, 0, empty:seq.symbol, i64)

Export code(match5)seq.symbol

Export functype(match5)llvmtype

Export type:symbol

Function parametertypes(m:match5)seq.word // used for records and loopblock // fsig.sym.m + module.sym.m

Export type:program

Function_(m:seq.match5, d:symbol)match5
 let e = findtemplate.d
  assert not.isempty.e report"LL" + fsig.d + module.d
   e_1

function =(a:match5, b:match5)boolean sym.a = sym.b

function hash(a:match5)int fsighash.sym.a

function assignencoding(l:int, a:match5)int l + 1

Function options(match5map:seq.match5, m:match5)seq.word options.code.m

Function funcdec(alltypes:typedict, i:symbol)int
 toint
 .modulerecord([ mangledname.i], [ toint.FUNCTIONDEC, typ.tollvmtype(alltypes, i), 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])

Function match5map(
theprg:program, uses:set.symbol, alltypes:typedict)seq.match5
 let discard3 = [ addtemplate(symbol("tocstr(bits seq)","builtin","cstr"), 2,
   GEP(r.1, i64, slot.ibcsub1, C64.2)  + CAST(r.2, r.1,  i64, ptrtoint))
 , addtemplate(symbol("bitcast(int seq seq)","builtin","int seq"), 0, emptyinternalbc)
 , addtemplate(symbol("bitcast(ptr)","builtin","int"), 1, CAST(r.1, slot.ibcsub1, i64, ptrtoint))
 , addtemplate(symbol("bitcast(int seq)","builtin","int"), 1, CAST(r.1, slot.ibcsub1, i64, ptrtoint))
 , addtemplate(symbol("bitcast(int)","builtin","int seq"), 1, CAST(r.1, slot.ibcsub1, ptr.i64, inttoptr))
 , addtemplate(symbol("nullptr","builtin","ptr"), 1, CAST(r.1, C64.0, ptr.i64, inttoptr))
 , addtemplate(symbol("IDX(T seq, int)","int builtin","int"), 2, GEP(r.1, i64, slot.ibcsub1, slot.ibcsub2) + LOAD(r.2, r.1, i64))
 , addtemplate(symbol("IDX(T seq, int)","ptr builtin","ptr"), 3, GEP(r.1, i64, slot.ibcsub1, slot.ibcsub2) + LOAD(r.2, r.1, i64)
 + CAST(r.3, r.2, ptr.i64, inttoptr))
 , addtemplate(symbol("IDX(T seq, int)","real builtin","real"), 3, GEP(r.1, i64, slot.ibcsub1, slot.ibcsub2) + LOAD(r.2, r.1, i64)
 + CAST(r.3, r.2, double, bitcast))
 , addtemplate(symbol("STKRECORD(ptr, ptr)","builtin","ptr"), 3, ALLOCA(r.1, ptr.ptr.i64, i64, C64.2, 0) + STORE(r.2, r.1, slot.ibcsub1)
 + GEP(r.2, ptr.i64, r.1, C64.1)
 + STORE(r.3, r.2, slot.ibcsub2)
 + GEP(r.3, ptr.i64, r.1, C64.0))
 , addtemplate(symbol("intpart(real)","builtin","real"), 1, CAST(r.1, slot.ibcsub1, i64, fptosi))
 , addtemplate(symbol("toreal(int)","builtin","real"), 1, CAST(r.1, slot.ibcsub1, double, sitofp))
 , addtemplate(symbol("-(real, real)","builtin","real"), 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, sub))
 , addtemplate(symbol("+(real, real)","builtin","real"), 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, add))
 , addtemplate(symbol("*(real, real)","builtin","real"), 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, mul))
 , addtemplate(symbol("/(real, real)","builtin","real"), 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, sdiv))
 , addtemplate(symbol("casttoreal(int)","builtin","real"), 1, CAST(r.1, slot.ibcsub1, double, bitcast))
 , addtemplate(symbol("representation(real)","builtin","int"), 1, CAST(r.1, slot.ibcsub1, i64, bitcast))
 , addtemplate(symbol("?(real, real)","builtin","ordering"), 5, CMP2(r.1, slot.ibcsub1, slot.ibcsub2, 3) + CAST(r.2, r.1, i64, zext)
 + CMP2(r.3, slot.ibcsub1, slot.ibcsub2, 2)
 + CAST(r.4, r.3, i64, zext)
 + BINOP(r.5, r.2, r.4, add))
 , addtemplate(symbol("?(int, int)","builtin","ordering"), 5, CMP2(r.1, slot.ibcsub1, slot.ibcsub2, 39) + CAST(r.2, r.1, i64, zext)
 + CMP2(r.3, slot.ibcsub1, slot.ibcsub2, 38)
 + CAST(r.4, r.3, i64, zext)
 + BINOP(r.5, r.2, r.4, add))
 , addtemplate(symbol("cast(T seq, int, int)","builtin","ptr"), 1, GEP(r.1, i64, slot.ibcsub1, slot.ibcsub2))
 , addtemplate(symbol(">(int, int)","builtin","boolean"), 2, CMP2(r.1, slot.ibcsub1, slot.ibcsub2, 38) + CAST(r.2, r.1, i64, zext))
 , addtemplate(symbol("not(boolean)","builtin","boolean"), 1, BINOP(r.1, slot.ibcsub1, C64.1, xor))
 , // include aborted here so does not show up in profile results addtemplate("abortedZbuiltinZTzprocess"_1, 1, CALL(1, 0, 32768, typ.function.[ i64, i64, i64], C."abortedZbuiltinZTzprocess",-1, ibcsub1)), Including this as a template causes subtle compile errors //
 addtemplate(symbol("=(int, int)","builtin","boolean"), 2, CMP2(r.1, slot.ibcsub1, slot.ibcsub2, 32) + CAST(r.2, r.1, i64, zext))
 , addtemplate(symbol("-(int, int)","builtin","int"), 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, sub))
 , addtemplate(symbol("+(int, int)","builtin","int"), 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, add))
 , addtemplate(symbol("*(int, int)","builtin","int"), 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, mul))
 , addtemplate(symbol("/(int, int)","builtin","int"), 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, sdiv))
 , addtemplate(symbol("<<(bits, int)","builtin","bits"), 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, shl))
 , addtemplate(symbol(">>(bits, int)","builtin","bits"), 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, lshr))
 , addtemplate(symbol("∧(bits, bits)","builtin","bits"), 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, and))
 , addtemplate(symbol("∨(bits, bits)","builtin","bits"), 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, or))
 , addtemplate(symbol("xor(bits, bits)","builtin","bits"), 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, xor))
 , addtemplate(symbol("setfirst(int seq, int, int)","builtin","int seq"), 3, GEP(r.1, i64, slot.ibcsub1, C64.1) + STORE(r.2, r.1, slot.ibcsub3)
 + GEP(r.2, i64, slot.ibcsub1, C64.0)
 + STORE(r.3, r.2, slot.ibcsub2)
 + GEP(r.3, i64, slot.ibcsub1, C64.0))
 , addtemplate(symbol("setfld(int, T seq, T)","int builtin","int"), 2, GEP(r.1, i64, slot.ibcsub2, slot.ibcsub1) + STORE(r.2, r.1, slot.ibcsub3)
 + BINOP(r.2, slot.ibcsub1, C64.1, add))
 , addtemplate(symbol("setfld(int, T seq, T)","real builtin","int"), 3, CAST(r.1, slot.ibcsub3, i64, bitcast) + GEP(r.2, i64, slot.ibcsub2, slot.ibcsub1)
 + STORE(r.3, r.2, r.1)
 + BINOP(r.3, slot.ibcsub1, C64.1, add))
 , addtemplate(symbol("setfld(int, T seq, T)","ptr builtin","int"), 3, CAST(r.1, slot.ibcsub2, ptr.ptr.i64, bitcast) + GEP(r.2, ptr.i64, r.1, slot.ibcsub1)
 + STORE(r.3, r.2, slot.ibcsub3)
 + BINOP(r.3, slot.ibcsub1, C64.1, add))
 , addtemplate(symbol("assert(word seq)","int builtin","int")
 , 1
 , CALL(r.1, 0, 32768, function.[ i64, i64, ptr.i64], symboltableentry("assert"_1, function.[ i64, i64, ptr.i64]), slot.ibcfirstpara2, slot.ibcsub1))
 , addtemplate(symbol("assert(word seq)","real builtin","real")
 , 2
 , CALL(r.1, 0, 32768, function.[ i64, i64, ptr.i64], symboltableentry("assert"_1, 
   function.[ i64, i64, ptr.i64]), slot.ibcfirstpara2, slot.ibcsub1)
   +CAST(r.2, r.1, double, sitofp))
 , addtemplate(symbol("assert(word seq)","ptr builtin","ptr")
 , 2
 , CALL(r.1, 0, 32768, function.[ i64, i64, ptr.i64], symboltableentry("assert"_1, 
 function.[ i64, i64, ptr.i64]), slot.ibcfirstpara2, slot.ibcsub1)
 +CAST(r.2, r.1,ptr.i64, inttoptr))
 ,//  
   Did not work because ibcfirstpara2 was not working correctly 
   addtemplate(symbol("callidx2(T seq,int)","int builtin","int"),4
 , GEP(r.1, i64, slot.ibcsub1, C64.0) 
 + LOAD(r.2, r.1, i64) 
 + CAST(r.3, r.2, ptr.function.[  i64, i64,ptr.i64, i64], inttoptr)
 + CALL(r.4, 0, 32768, function.[ i64, i64, ptr.i64, i64], r.3, 
  slot.ibcfirstpara2 , slot.ibcsub1, slot.ibcsub2 ))
, addtemplate(symbol("callidx2(T seq,int) ","real builtin","real"),4
 , GEP(r.1, i64, slot.ibcsub1, C64.0) 
 + LOAD(r.2, r.1, i64) 
 + CAST(r.3, r.2, ptr.function.[  double, i64,ptr.i64, i64], inttoptr)
 + CALL(r.4, 0, 32768, function.[ double, i64, ptr.i64, i64], r.3, 
  slot.ibcfirstpara2, [slot.ibcsub1, slot.ibcsub2]))
, addtemplate(symbol("callidx2(T seq,int) ","ptr builtin","ptr"),4
 , GEP(r.1, i64, slot.ibcsub1, C64.0) 
 + LOAD(r.2, r.1, i64) 
 + CAST(r.3, r.2, ptr.function.[  ptr.i64, i64,ptr.i64, i64], inttoptr)
 + CALL(r.4, 0, 32768, function.[ ptr.i64, i64, ptr.i64, i64], r.3, 
  slot.ibcfirstpara2, [slot.ibcsub1, slot.ibcsub2])) //
   addtemplate(symbol("callidx3(T seq,int)","int builtin","int")
 , 1
 , CALL(r.1, 0, 32768, function.[ i64, i64, ptr.i64, i64], symboltableentry("callidx3"_1, 
 function.[ i64, i64, ptr.i64, i64]), slot.ibcfirstpara2, slot.ibcsub1,slot.ibcsub2))
 , addtemplate(symbol("callidx3(T seq,int)","real builtin","real")
 , 2
 , CALL(r.1, 0, 32768, function.[ i64, i64, ptr.i64, i64], symboltableentry("callidx3"_1, 
   function.[ i64, i64, ptr.i64, i64]), slot.ibcfirstpara2, slot.ibcsub1 ,slot.ibcsub2)
   +CAST(r.2, r.1, double, sitofp))
 , addtemplate(symbol("callidx3(T seq,int)","ptr builtin","ptr")
 , 2
 , CALL(r.1, 0, 32768, function.[ i64, i64, ptr.i64, i64], symboltableentry("callidx3"_1, 
 function.[ i64, i64, ptr.i64, i64]), slot.ibcfirstpara2, slot.ibcsub1,slot.ibcsub2)
 +CAST(r.2, r.1,ptr.i64, inttoptr))
 ]
 let const = toseq.uses @ +(empty:seq.symbol, buildtemplate(theprg, alltypes, @e))
 let discard4 = processconst(const, 1, empty:seq.symbol)
  empty:seq.match5
  

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
  let e = findtemplate.xx
   if isempty.e then empty:seq.int else processconstargs(arglist, i + 1, args + arg.e_1)

function processconst(toprocess:seq.symbol, i:int, notprocessed:seq.symbol)seq.match5
 if i > length.toprocess then
 if isempty.notprocessed then empty:seq.match5 else processconst(notprocessed, 1, empty:seq.symbol)
 else
  let xx = toprocess_i
  let args = processconstargs(constantcode.xx, 1, empty:seq.int)
   if isempty.args then processconst(toprocess, i + 1, notprocessed + toprocess_i)
   else
    let discard = encode.addtemplate(xx, 0, empty:seq.templatepart,"ACTARG"_1, slot.addobject.args)
     processconst(toprocess, i + 1, notprocessed)

function buildtemplate(theprg:program, alltypes:typedict, xx:symbol)seq.symbol
 let pkg = module.xx
  if pkg = "$constant"then [ xx]
  else
   let discard1 = if isFref.xx then
   let mn = mangledname.(constantcode.xx)_1
    let functyp = ptr.tollvmtype(alltypes,(constantcode.xx)_1)
     addtemplate(xx, 0, empty:seq.templatepart,"ACTARG"_1, ptrtoint(functyp, symboltableentry(mn, functyp)))
   else if islit.xx then
   addtemplate(xx, 0, empty:seq.templatepart,"ACTARG"_1, if pkg = "$real"then Creal.toint.(fsig.xx)_1 else C64.toint.(fsig.xx)_1)
   else if islocal.xx then addtemplate(xx, 0, empty:seq.templatepart,"LOCAL"_1, slot.toint.(fsig.xx)_1)
   else if isdefine.xx then addtemplate(xx, 0, empty:seq.templatepart,(fsig.xx)_1, slot.toint.(fsig.xx)_2)
   else if isblock.xx then
   let typ = tollvmtype(alltypes, resulttype.xx)
     addtemplate(xx, 0, empty:seq.templatepart,(fsig.xx)_1, nopara.xx, empty:seq.symbol, typ)
   else if isspecial.xx then addtemplate(xx, 0, empty:seq.templatepart,(fsig.xx)_1, slot.nopara.xx)
   else if pkg = "$words"then addtemplate(xx, 0, empty:seq.templatepart,"ACTARG"_1, slot.addwordseq2.fsig.xx)
   else if pkg = "$word"then
   addtemplate(xx, 0, empty:seq.templatepart,"ACTARG"_1, slot.wordref.(fsig.xx)_1)
   else if not(abstracttype.modname.xx = "builtin"_1)then
   call(alltypes, xx,"CALL"_1, code.lookupcode(theprg, xx), mangledname.xx)
   else
    // handle builtin package //
    let intable = findtemplate.xx
     if length.intable > 0 then intable_1
      else if(fsig.xx)_1 = "global"_1 then
     addtemplate(xx, 1, GEP(r.1, i64, slot.global([ mangledname.xx], i64, C64.0)))
     else if isexternal.xx then
     let symname = if(fsig.xx)_1 ∈ "arcsin"then"asin"_1
      else if(fsig.xx)_1 ∈ "arccos"then"acos"_1 else(fsig.xx)_1
       call(alltypes, xx,"CALLE"_1, empty:seq.symbol, symname)
     else
      let symname = if(fsig.xx)_1 ∈ "assert"then"assert"_1 else mangledname.xx
       call(alltypes, xx,"CALL"_1, code.lookupcode(theprg, xx), symname)
    empty:seq.symbol

function call(alltypes:typedict, xx:symbol, type:word, code:seq.symbol, symname:word)match5
 let functype = tollvmtype(alltypes, xx)
 let newcode = CALLSTART(1, 0, 32768, typ.functype, toint.symboltableentry(symname, functype), if type = "CALL"_1 then nopara.xx + 1 else nopara.xx)
  addtemplate(xx, 1, getparts.newcode, type, nopara.xx, code, functype)

Function usetemplate(t:match5, deltaoffset:int, argstack:seq.int)internalbc
 let args = if action.t = "CALL"_1 then empty:seq.int
 else subseq(argstack, length.argstack - arg.t + 1, length.argstack)
  processtemplate(parts.t, deltaoffset, args)