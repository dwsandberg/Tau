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

use internalbc

use textio

Export constdata seq.slot

Export wordref(w:word)int

Export addliblib(libname:seq.word, mods:int, profiledata:int,isbase:boolean)int

Function isbuiltinlist(sym:symbol) boolean  
 fsig.sym &in  ["+(real,real)","*(real,real)"
,"-(real,real)","/(real,real)","?(real,real)",">>(bits, int)","<<(bits, int)"
,"∧(bits, bits)","∨(bits, bits)","xor(bits, bits)","-(int,int)","+(int,int)","*(int, int)","/(int,int)" 
,"=(int,int)","=(boolean,boolean)",">(int,int)","?(int,int)"  ,"representation(real)", "casttoreal(int)","not(boolean)" 
,"toint(byte)","toint(bit)","toreal(int)","intpart(real)" ,"tocstr(bits seq)"
,"bitcast(int seq)","bitcast(int)","GEP(int seq, int)","false","true"]
&or  module.sym="$internal"

Function mangledname(s:symbol)word  mangle(fsig.s, module.s)

Function tollvmtype(alltypes:typedict, s:symbol)llvmtype
 if fsig.s = "option(T, word seq)"then function.constantseq(nopara.s + 2, i64)
 else
   function.tollvmtypelist(alltypes,s)
   
Function tollvmtypelist(alltypes:typedict, s:symbol) seq.llvmtype
  let starttypes = //  if      fsig.s &in Externalsyms   then  [ tollvmtype(alltypes, resulttype.s)]
  else  // [ tollvmtype(alltypes, resulttype.s), i64]
paratypes.s @ +(starttypes, tollvmtype(alltypes, @e))

function tollvmtype(alltypes:typedict, s:mytype)llvmtype
 let kind = kind.gettypeinfo(alltypes, s)
  if kind = "int boolean"_1 then i64 else if kind = "real"_1 then double else ptr.i64

Function conststype llvmtype array(-2, i64)

Function profiletype llvmtype array(-3, i64)

Export type:match5

Export length(match5)int // no of instruction that return results //

Export action(match5)word

Export arg(match5)int

type match5 is record sym:symbol, length:int, parts:internalbc, action:word, arg:int, code:seq.symbol, functype:llvmtype

function addtemplate(sym:symbol, length:int, parts:internalbc, action:word, arg:int, code:seq.symbol, functype:llvmtype)match5
 let m = match5(sym, length, parts, action, arg, code, functype)
 let discard = encode.m
  m

function addtemplate(sym:symbol, length:int, parts:internalbc, action:word, arg:slot)match5
 addtemplate(sym, length, parts, action, toint.arg, empty:seq.symbol, i64)

function addtemplate(sym:symbol, length:int, b:internalbc)match5 
addtemplate(sym, length,    b,"TEMPLATE"_1, slot.nopara.sym)

function findtemplate(d:symbol)seq.match5 findencode.match5(d, 0, emptyinternalbc,"NOTFOUND"_1, 0, empty:seq.symbol, i64)

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

Function options(match5map:seq.match5, m:match5)seq.word getoption.code.m

Function funcdec(alltypes:typedict, i:symbol)int
 toint
 .modulerecord([ mangledname.i], [ toint.FUNCTIONDEC, typ.tollvmtype(alltypes, i), 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])

Function match5map(
theprg:program, uses:set.symbol, alltypes:typedict)seq.match5
 let discard3 = [ addtemplate(symbol("extractbyte(int seq,int)","internal","int"),8,
    BINOP(r.1,ibcsub.2,C64.3,lshr)
   +BINOP(r.2,r.1,C64.2,add)
   + GEP(r.3, i64, ibcsub.1, r.2) 
   + LOAD(r.4, r.3, i64)
  +BINOP(r.5, ibcsub.2, C64.7, and)
  +BINOP(r.6, r.5, C64.3, shl)
  +BINOP(r.7,r.4,r.6,lshr)
  +BINOP(r.8,r.7,C64.255,and)
  )
  ,addtemplate(symbol("extractbit(int seq,int)","internal","int"),7,
    BINOP(r.1,ibcsub.2,C64.6,lshr)
      +BINOP(r.2,r.1,C64.2,add)
   + GEP(r.3, i64, ibcsub.1, r.2) 
   + LOAD(r.4, r.3, i64)
   +BINOP(r.5, ibcsub.2, C64.63, and)
   +BINOP(r.6,r.4,r.5,lshr)
  +BINOP(r.7,r.6,C64.1,and)
  )
 ,addtemplate(symbol("tocstr(bits seq)","fileio","cstr"), 2,
   GEP(r.1, i64, ibcsub.1, C64.2)  + CAST(r.2, r.1,  i64, ptrtoint))
 , addtemplate(symbol("toint(byte)","bits","int"), 1, BINOP(r.1, ibcsub.1, C64.0, add))
 , addtemplate(symbol("toint(bit)","bits","int"), 1, BINOP(r.1, ibcsub.1, C64.0, add))
 , // addtemplate(NullptrOp, 1, CAST(r.1, C64.0, ptr.i64, inttoptr))
 ,  addtemplate( STKRECORDOp, 3, ALLOCA(r.1, ptr.ptr.i64, i64, C64.2, 0) + STORE(r.2, r.1, ibcsub.1)
 + GEP(r.2, ptr.i64, r.1, C64.1)
 + STORE(r.3, r.2, ibcsub.2)
 + GEP(r.3, ptr.i64, r.1, C64.0))
 ,addtemplate(symbol("bitcast(ptr)","builtin","int"), 1, CAST(r.1, ibcsub.1, i64, ptrtoint))
 ,  addtemplate(symbol("bitcast(int seq)","interpreter","int"), 1, CAST(r.1, ibcsub.1, i64, ptrtoint))
 , // addtemplate(symbol("GEP(int seq, int)","interpreter","int"), 2, GEP(r.1, i64, ibcsub.1, ibcsub.2)
 +CAST(r.2, r.1, i64, ptrtoint))
, addtemplate(symbol("bitcast(int)","interpreter","int seq"), 1, CAST(r.1, ibcsub.1, ptr.i64, inttoptr))
 , addtemplate(symbol("IDX2(int seq, int)","int abstractBuiltin","int"), 2, GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64))
  , addtemplate(symbol("IDX2(boolean seq, int)","boolean abstractBuiltin","boolean"), 2, GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64))
, addtemplate(symbol("IDX2(ptr seq, int)","ptr abstractBuiltin","ptr"), 3, 
   GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64)+ CAST(r.3, r.2, ptr.i64, inttoptr))
 , addtemplate(symbol("IDX2(real seq, int)","real abstractBuiltin","real"), 3, 
 GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64)+ CAST(r.3, r.2, double, bitcast))
 ,  addtemplate(symbol("intpart(real)","real","real"), 1, CAST(r.1, ibcsub.1, i64, fptosi))
 , addtemplate(symbol("toreal(int)","real","real"), 1, CAST(r.1, ibcsub.1, double, sitofp))
 , addtemplate(symbol("-(real, real)","real","real"), 1, BINOP(r.1, ibcsub.1, ibcsub.2, sub))
  , addtemplate(symbol("+(real, real)","real","real"), 1, BINOP(r.1, ibcsub.1, ibcsub.2, add))
  , addtemplate(symbol("*(real, real)","real","real"), 1, BINOP(r.1, ibcsub.1, ibcsub.2, mul))
 , addtemplate(symbol("/(real, real)","real","real"), 1, BINOP(r.1, ibcsub.1, ibcsub.2, sdiv))
 , addtemplate(symbol("casttoreal(int)","real","real"), 1, CAST(r.1, ibcsub.1, double, bitcast))
 , addtemplate(symbol("representation(real)","real","int"), 1, CAST(r.1, ibcsub.1, i64, bitcast))
 , addtemplate(symbol("?(real, real)","real","ordering"), 5, CMP2(r.1, ibcsub.1, ibcsub.2, 3) + CAST(r.2, r.1, i64, zext)
 + CMP2(r.3, ibcsub.1, ibcsub.2, 2)
 + CAST(r.4, r.3, i64, zext)
 + BINOP(r.5, r.2, r.4, add))
 , addtemplate(symbol("?(int, int)","standard","ordering"), 5, CMP2(r.1, ibcsub.1, ibcsub.2, 39) + CAST(r.2, r.1, i64, zext)
 + CMP2(r.3, ibcsub.1, ibcsub.2, 38)
 + CAST(r.4, r.3, i64, zext)
 + BINOP(r.5, r.2, r.4, add))
   , addtemplate(symbol("GEP(ptr seq, int)","internal","ptr"), 1, GEP(r.1, i64, ibcsub.1, ibcsub.2))
  , addtemplate(symbol("not(boolean)","standard","boolean"), 1, BINOP(r.1, ibcsub.1, C64.1, xor))
 , addtemplate(symbol(">(int, int)","standard","boolean"), 2, CMP2(r.1, ibcsub.1, ibcsub.2, 38) + CAST(r.2, r.1, i64, zext))
 , addtemplate(symbol("=(boolean, boolean)","standard","boolean"), 2, CMP2(r.1, ibcsub.1, ibcsub.2, 32) + CAST(r.2, r.1, i64, zext))
 , addtemplate(symbol("=(int, int)","standard","boolean"), 2, CMP2(r.1, ibcsub.1, ibcsub.2, 32) + CAST(r.2, r.1, i64, zext))
,  addtemplate(symbol("-(int, int)","standard","int"), 1, BINOP(r.1, ibcsub.1, ibcsub.2, sub))
 ,addtemplate(symbol("+(int, int)","standard","int"), 1, BINOP(r.1, ibcsub.1, ibcsub.2, add))
 ,   addtemplate(symbol("*(int, int)","standard","int"), 1, BINOP(r.1, ibcsub.1, ibcsub.2, mul))
 ,   addtemplate(symbol("/(int, int)","standard","int"), 1, BINOP(r.1, ibcsub.1, ibcsub.2, sdiv))  
,   addtemplate(symbol("<<(bits, int)","bits","bits"), 1, BINOP(r.1, ibcsub.1, ibcsub.2, shl))
 , addtemplate(symbol(">>(bits, int)","bits","bits"), 1, BINOP(r.1, ibcsub.1, ibcsub.2, lshr))
 , addtemplate(symbol("∧(bits, bits)","bits","bits"), 1, BINOP(r.1, ibcsub.1, ibcsub.2, and))
 , addtemplate(symbol("∨(bits, bits)","bits","bits"), 1, BINOP(r.1, ibcsub.1, ibcsub.2, or))
 , addtemplate(symbol("xor(bits, bits)","bits","bits"), 1, BINOP(r.1, ibcsub.1, ibcsub.2, xor))
 , addtemplate(symbol("setfirst(T seq, int, int)","real builtin","T seq"), 3, GEP(r.1, i64, ibcsub.1, C64.1) + STORE(r.2, r.1, ibcsub.3)
  + GEP(r.2, i64, ibcsub.1, C64.0)
 + STORE(r.3, r.2, ibcsub.2)
 + GEP(r.3, i64, ibcsub.1, C64.0))
 , addtemplate(symbol("setfirst(T seq, int, int)","ptr builtin","T seq"), 3, GEP(r.1, i64, ibcsub.1, C64.1) + STORE(r.2, r.1, ibcsub.3)
 + GEP(r.2, i64, ibcsub.1, C64.0)
 + STORE(r.3, r.2, ibcsub.2)
 + GEP(r.3, i64, ibcsub.1, C64.0))
 , addtemplate(symbol("setfirst(T seq, int, int)","int builtin","T seq"), 3, GEP(r.1, i64, ibcsub.1, C64.1) + STORE(r.2, r.1, ibcsub.3)
 + GEP(r.2, i64, ibcsub.1, C64.0)
 + STORE(r.3, r.2, ibcsub.2)
 + GEP(r.3, i64, ibcsub.1, C64.0))
  , addtemplate(symbol("setfld(int, int seq, int)","$internal","int"), 2, GEP(r.1, i64, ibcsub.2, ibcsub.1) + STORE(r.2, r.1, ibcsub.3)
 + BINOP(r.2, ibcsub.1, C64.1, add))
 , addtemplate(symbol("setfld(int, boolean seq, boolean)","$internal","boolean"), 2, GEP(r.1, i64, ibcsub.2, ibcsub.1) + STORE(r.2, r.1, ibcsub.3)
 + BINOP(r.2, ibcsub.1, C64.1, add))
 , addtemplate(symbol("setfld(int, real seq, real)","$internal","int"), 3, CAST(r.1, ibcsub.3, i64, bitcast) + GEP(r.2, i64, ibcsub.2, ibcsub.1)
 + STORE(r.3, r.2, r.1)
 + BINOP(r.3, ibcsub.1, C64.1, add))
  , addtemplate(symbol("setfld(int, ptr seq, ptr)","$internal","int"), 3, CAST(r.1, ibcsub.2, ptr.ptr.i64, bitcast) + GEP(r.2, ptr.i64, r.1, ibcsub.1)
 + STORE(r.3, r.2, ibcsub.3)
 + BINOP(r.3, ibcsub.1, C64.1, add))
, addtemplate(symbol("setfld(int, T seq, T)","int builtin","int"), 2, GEP(r.1, i64, ibcsub.2, ibcsub.1) + STORE(r.2, r.1, ibcsub.3)
 + BINOP(r.2, ibcsub.1, C64.1, add))
, addtemplate(symbol("setfld(int, T seq, T)","boolean builtin","boolean"), 2, GEP(r.1, i64, ibcsub.2, ibcsub.1) + STORE(r.2, r.1, ibcsub.3)
 + BINOP(r.2, ibcsub.1, C64.1, add))
 , addtemplate(symbol("setfld(int, T seq, T)","real builtin","int"), 3, CAST(r.1, ibcsub.3, i64, bitcast) + GEP(r.2, i64, ibcsub.2, ibcsub.1)
 + STORE(r.3, r.2, r.1)
 + BINOP(r.3, ibcsub.1, C64.1, add))
 , addtemplate(symbol("setfld(int, T seq, T)","ptr builtin","int"), 3, CAST(r.1, ibcsub.2, ptr.ptr.i64, bitcast) + GEP(r.2, ptr.i64, r.1, ibcsub.1)
 + STORE(r.3, r.2, ibcsub.3)
 + BINOP(r.3, ibcsub.1, C64.1, add))
 , addtemplate(symbol("assert:int(word seq)","builtin","int")
 , 1
 , CALL(r.1, 0, 32768, function.[ i64, i64, ptr.i64], symboltableentry("assert"_1, function.[ i64, i64, ptr.i64]), slot.ibcfirstpara2, ibcsub.1))
 , addtemplate(symbol("assert:boolean(word seq)","builtin","boolean")
 , 1
 , CALL(r.1, 0, 32768, function.[ i64, i64, ptr.i64], symboltableentry("assert"_1, function.[ i64, i64, ptr.i64]), slot.ibcfirstpara2, ibcsub.1))
 , addtemplate(symbol("assert:real(word seq)","builtin","real")
 , 2
 , CALL(r.1, 0, 32768, function.[ i64, i64, ptr.i64], symboltableentry("assert"_1, 
   function.[ i64, i64, ptr.i64]), slot.ibcfirstpara2, ibcsub.1)
   +CAST(r.2, r.1, double, sitofp))
 , addtemplate(symbol("assert:ptr(word seq)","builtin","ptr")
 , 2
 , CALL(r.1, 0, 32768, function.[ i64, i64, ptr.i64], symboltableentry("assert"_1, 
 function.[ i64, i64, ptr.i64]), slot.ibcfirstpara2, ibcsub.1)
 +CAST(r.2, r.1,ptr.i64, inttoptr))
 ,     addtemplate(symbol("callidx2(T seq,int)","int builtin","int"),4
 , GEP(r.1, i64, ibcsub.1, C64.0) 
 + LOAD(r.2, r.1, i64) 
 + CAST(r.3, r.2, ptr.function.[  i64, i64,ptr.i64, i64], inttoptr)
 + CALL(r.4, 0, 32768, function.[ i64, i64, ptr.i64, i64], r.3, 
  slot.ibcfirstpara2 , ibcsub.1, ibcsub.2 ))
, addtemplate(symbol("callidx2(T seq,int) ","real builtin","real"),4
 , GEP(r.1, i64, ibcsub.1, C64.0) 
 + LOAD(r.2, r.1, i64) 
 + CAST(r.3, r.2, ptr.function.[  double, i64,ptr.i64, i64], inttoptr)
 + CALL(r.4, 0, 32768, function.[ double, i64, ptr.i64, i64], r.3, 
  slot.ibcfirstpara2, [ibcsub.1, ibcsub.2]))
, addtemplate(symbol("callidx2(T seq,int) ","ptr builtin","ptr"),4
 , GEP(r.1, i64, ibcsub.1, C64.0) 
 + LOAD(r.2, r.1, i64) 
 + CAST(r.3, r.2, ptr.function.[  ptr.i64, i64,ptr.i64, i64], inttoptr)
 + CALL(r.4, 0, 32768, function.[ ptr.i64, i64, ptr.i64, i64], r.3, 
  slot.ibcfirstpara2, [ibcsub.1, ibcsub.2]))  
 ,     addtemplate(symbol("callidx(int seq,int)","$internal","int"),4
 , GEP(r.1, i64, ibcsub.1, C64.0) 
 + LOAD(r.2, r.1, i64) 
 + CAST(r.3, r.2, ptr.function.[  i64, i64,ptr.i64, i64], inttoptr)
 + CALL(r.4, 0, 32768, function.[ i64, i64, ptr.i64, i64], r.3, 
  slot.ibcfirstpara2 , ibcsub.1, ibcsub.2 ))
, addtemplate(symbol("callidx(real seq,int) ","$internal","real"),4
 , GEP(r.1, i64, ibcsub.1, C64.0) 
 + LOAD(r.2, r.1, i64) 
 + CAST(r.3, r.2, ptr.function.[  double, i64,ptr.i64, i64], inttoptr)
 + CALL(r.4, 0, 32768, function.[ double, i64, ptr.i64, i64], r.3, 
  slot.ibcfirstpara2, [ibcsub.1, ibcsub.2]))
, addtemplate(symbol("callidx(ptr,int) ","$internal","ptr"),4
 , GEP(r.1, i64, ibcsub.1, C64.0) 
 + LOAD(r.2, r.1, i64) 
 + CAST(r.3, r.2, ptr.function.[  ptr.i64, i64,ptr.i64, i64], inttoptr)
 + CALL(r.4, 0, 32768, function.[ ptr.i64, i64, ptr.i64, i64], r.3, 
  slot.ibcfirstpara2, [ibcsub.1, ibcsub.2]))  
 ]
 let const = toseq.(uses -asset.[Optionsym]) @ +(empty:seq.symbol, buildtemplate(theprg, alltypes, @e))
 let discard4 = processconst(const, 1, empty:seq.symbol)
  empty:seq.match5
  

function symboltableentry(name:word)slot symboltableentry(name, i64)

Function symboltableentry(name:word, type:llvmtype)slot symboltableentry([ name], type)

Function symboltableentry(name:seq.word, type:llvmtype)slot
 modulerecord(name, [ toint.FUNCTIONDEC, typ.type, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])


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
    let discard = encode.addtemplate(xx, 0, emptyinternalbc,"ACTARG"_1, slot.addobject.args)
     processconst(toprocess, i + 1, notprocessed)
     
     function =(a:llvmtype,b:llvmtype) boolean typ.a=typ.b
     
     use set.mytype
  
function buildtemplate(theprg:program, alltypes:typedict, xx:symbol)seq.symbol
 let pkg = module.xx
  if pkg = "$constant"then [ xx]
  else
   let discard1 = if isFref.xx then
     let f1=(constantcode.xx)_1
   //  assert  double &nin tollvmtypelist(alltypes,f1) 
       &or fsig.f1 &in [
       "_(typereal pseq, int)","_(real pseq, int)","_(real blockseq, int)","_(typereal cseq, int)"]
       report "FREF to real function"+print.xx //
   let mn = mangledname.f1
    let functyp = ptr.tollvmtype(alltypes,f1)
     addtemplate(xx, 0, emptyinternalbc,"ACTARG"_1, ptrtoint(functyp, symboltableentry(mn, functyp)))
   else if islit.xx then
   addtemplate(xx, 0, emptyinternalbc,"ACTARG"_1, if pkg = "$real"then Creal.value.xx else C64.value.xx)
   else if islocal.xx then addtemplate(xx, 0, emptyinternalbc,"LOCAL"_1, slot.value.xx)
   else if isdefine.xx then addtemplate(xx, 0, emptyinternalbc,(fsig.xx)_1, slot.toint.(fsig.xx)_2)
   else if isblock.xx then
   let typ = tollvmtype(alltypes, resulttype.xx)
      addtemplate(xx, 0, emptyinternalbc,(fsig.xx)_1, nopara.xx, empty:seq.symbol, typ)
   else if isspecial.xx then   if (fsig.xx)_1 = "RECORD"_1  &and nopara.xx < 10 then 
      let fldbc=recordcode(arithseq(nopara.xx,1, ibcfirstpara2+1),fsig.xx,0,true)
     addtemplate(xx, regno.fldbc, bc.fldbc)
     else 
      addtemplate(xx, 0, emptyinternalbc,(fsig.xx)_1, slot.nopara.xx)
   else if pkg = "$words"then addtemplate(xx, 0, emptyinternalbc,"ACTARG"_1, slot.addwordseq2.fsig.xx)
   else if pkg = "$word"then
      addtemplate(xx, 0, emptyinternalbc,"ACTARG"_1, slot.wordref.(fsig.xx)_1)
   else
    // handle builtin package //
    let intable = findtemplate.xx
     if length.intable > 0 then intable_1
      else if(fsig.xx)_1 = "global"_1  &and module.xx="$global" then
     addtemplate(xx, 1, GEP(r.1, i64, slot.global([ mangledname.xx], i64, C64.0)))
     else //
       if   fsig.xx &in   Externalsyms then 
         call(alltypes, xx,"CALLE"_1, empty:seq.symbol, mangledname.xx) 
       else //
           call(alltypes, xx,"CALL"_1, code.lookupcode(theprg, xx), mangledname.xx)
    empty:seq.symbol

function call(alltypes:typedict, xx:symbol, type:word, code:seq.symbol, symname:word)match5
 let functype = tollvmtype(alltypes, xx)
 let newcode = CALLSTART(1, 0, 32768, typ.functype, toint.symboltableentry(symname, functype), if type = "CALL"_1 then nopara.xx + 1 else nopara.xx)
  addtemplate(xx, 1,  newcode, type, nopara.xx, code, functype)

Function usetemplate(t:match5, deltaoffset:int, argstack:seq.int)internalbc
 let args = if action.t = "CALL"_1 then empty:seq.int
 else subseq(argstack, length.argstack - arg.t + 1, length.argstack)
  processtemplate(parts.t, deltaoffset, args)
  
type recordcoderesult is record regno:int, bc:internalbc 

Export regno(recordcoderesult) int

Export bc(recordcoderesult) internalbc


function setnextfld(bc:internalbc, args:seq.int, i:int, types:seq.word,  regno:int, pint:int, preal:int, pptr:int) 
recordcoderesult
 if i > length.args then recordcoderesult(regno, bc)
 else
    let typ = types_(i * 2 + 1)
    if typ = "real"_1 then
        if preal=0 then
           setnextfld(bc + CAST(r(regno + 1), r.pint, ptr.double, bitcast), args, i, types,  regno + 1, pint, regno + 1, pptr)
        else 
           let newbc = GEP(r(regno + 1), double, r.preal, C64(i - 1))+ STORE(r(regno + 2), r(regno + 1), slot.args_i)
           setnextfld(bc + newbc, args, i + 1, types,  regno + 1, pint, preal, pptr)
     else if typ ∈ "ptr"then
      if pptr=0 then 
          setnextfld(bc + CAST(r(regno + 1), r.pint, ptr.ptr.i64, bitcast), args, i, types,   regno + 1, pint, preal, regno + 1)
      else 
        let newbc = GEP(r(regno + 1), ptr.i64, r.pptr, C64(i - 1))+ STORE(r(regno + 2), r(regno + 1), slot.args_i)
         setnextfld(bc + newbc, args, i + 1, types,  regno + 1, pint, preal, pptr)
     else
        assert typ ∈ "int boolean byte"  report"setnextfld problem" + typ
       let newbc = GEP(r(regno + 1), i64, r.pint, C64(i - 1))+ STORE(r(regno + 2), r(regno + 1), slot.args_i)
           setnextfld(bc + newbc, args, i + 1, types,  regno + 1, pint, preal, pptr)

Function   recordcode  (args:seq.int,   types:seq.word, lastreg:int, template:boolean) recordcoderesult
   let firstpara=if template then   slot.ibcfirstpara2 else r.1
   let newcode = CALL(r(lastreg + 1), 0, 32768, function.[ ptr.i64, i64, i64], symboltableentry("allocatespace", function.[ ptr.i64, i64, i64]), firstpara, C64.length.args)
    let c= setnextfld( newcode, args, 1, types,  lastreg + 1, lastreg + 1, 0, 0)
     if template then   recordcoderesult( regno.c+1,bc.c+GEP(r(regno.c+1),i64,r(lastreg+1),C64.0))
     else c
     
     