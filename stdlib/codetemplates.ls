Module program


use symbol

use seq.symbol

use seq.symdef

use standard

use seq.set.symdef

type program is datax:seq.set.symdef 

Function data(a:program) set.symdef  first.datax.a

Function program(s:set.symdef) program program.[s]

Function /cup(a:program,b:program) program 
  program (data.a /cup data.b )
    


Export type:program


Function getCode(theprg:program,s:symbol) seq.symbol 
 let f=findelement(symdef(s,empty:seq.symbol),data.theprg)
 if isempty.f then empty:seq.symbol else code.f_1
 
Function isdefined(theprg:program,s:symbol) boolean
 not.isempty.findelement(symdef(s,empty:seq.symbol),data.theprg)
  

Function print(p:program, i:symbol)seq.word  
  print.i + for acc ="", @e = getCode(p,i) do acc + print.@e /for(acc)


Function  target(a:symdef)symbol sym.a 

use seq.symdef
 
Function  tosymdefs(p:program)seq.symdef   toseq.data.p

Function emptyprogram program program.empty:set.symdef

Function map(p:program, s:symbol, code:seq.symbol)program 
program.replace(data.p,symdef(s,code)  )    

use set.symdef

use seq.mytype

use seq.symdef


use set.symbol


use mytype

use typerep


/type typerep is totypeseq:seq.mytype

/function ?(a:typerep,b:typerep) ordering  first.totypeseq.a ? first.totypeseq.b

use set.typerep

/function type(a:typerep) mytype  first.totypeseq.a

/function flatflds(a:typerep) seq.mytype  totypeseq.a << 1

/Export typerep(t:mytype,flat:seq.mytype) typerep  

type type2dict is totypedict:set.typerep

Function print(dict:type2dict) seq.word
   for txt="", tr=toseq.totypedict.dict do   for acc2=txt,  t=totypeseq.tr do acc2+print.t /for(acc2+EOL) /for(txt)

Export type:type2dict

Export totypedict(type2dict) set.typerep

Export type2dict(set.typerep) type2dict


Function emptytypedict type2dict type2dict.empty:set.typerep

Function add(alltypes:type2dict,t:mytype,flatflds:seq.mytype) type2dict
   type2dict(totypedict.alltypes +typerep(t,flatflds))
      

 
Function    flatflds(alltypes:type2dict,type:mytype) seq.mytype
  let t=  findelement(typerep(type,empty:seq.mytype),totypedict.alltypes)
  if isempty.t then empty:seq.mytype
  else flatflds.t_1  
  
Function    flatwithtype(alltypes:type2dict,type:mytype) seq.mytype
   let t=  findelement(typerep(type,empty:seq.mytype),totypedict.alltypes)
 if isempty.t then empty:seq.mytype
  else [type.t_1] +flatflds.t_1  
        
  
Function coretype(typ:mytype, alltypes:type2dict) mytype  coretype(typ,alltypes,0)
    
Function coretype(typ:mytype, alltypes:type2dict,maxsize:int)mytype
 if typ = typeint ∨ typ = typeboolean ∨ typ = typeptr ∨ typ = typereal
 ∨ typ = typeT then
  typ
 else if isseq.typ then typeptr
 else if isencoding.typ then typeint
 else
   let flatflds=flatflds(alltypes,typ)
  if isempty.flatflds then typ else 
  if length.flatflds = 1 then coretype(first.flatflds, alltypes)else
      if length.flatflds > maxsize then typeptr
      else  if length.flatflds = 2 then  typeref."packed2 tausupport . "
      else if length.flatflds = 3 then  typeref."packed3 tausupport . "
      else if length.flatflds = 4 then  typeref."packed4 tausupport . "
      else if length.flatflds = 5 then  typeref."packed5 tausupport . " 
      else typeref."packed6 tausupport . " 
 
  
 Function packedtypes seq.mytype [
typeref(  "packed2 tausupport .")
,typeref(  "packed3 tausupport .")
,typeref(  "packed4 tausupport .")
,typeref(  "packed5 tausupport .")
,typeref(  "packed6 tausupport .")
 ]

 
Function buildargcodeI(  sym:symbol)int
 { needed because the call interface implementation for reals is different than other types is some implementations }
 for acc = 1, typ = paratypes.sym + resulttype.sym do
  acc * 2
  + if  {getbasetype(alltypes, typ)} typ  = typereal then 1 else 0
 /for(acc)  

 ----
 
use encoding.symbol

use seq.symbolref

use seq.encodingpair.symbol

use seq.seq.mytype

use set.symbolref

use seq.seq.symbolref

use seq.seq.word

use seq.libraryModule


 type symbolref is toint:int

Export toint(symbolref)int

Export symbolref(int)symbolref

Export type:symbolref

Function symbolref(sym:symbol)symbolref symbolref.valueofencoding.encode.sym

Function assignencoding(l:seq.encodingpair.symbol  , symbol) int  length.l+1

Function symbolrefdecode seq.symbol
  for acc=empty:seq.symbol , p=encoding:seq.encodingpair.symbol do
              acc+data.p
        /for(acc)



type libraryModule is modname:modref, exports:seq.symbolref,
uses:seq.mytype,defines:seq.symbolref,types:seq.seq.mytype

Export libraryModule ( modname:modref, exports:seq.symbolref,
uses:seq.mytype,defines:seq.symbolref,types:seq.seq.mytype)libraryModule

Export type:libraryModule


Export   exports(libraryModule)  seq.symbolref

Export modname(libraryModule) modref

Export uses(libraryModule) seq.mytype

Export defines(libraryModule)  seq.symbolref

Export types(libraryModule) seq.seq.mytype


Export alltypes(compileinfo)type2dict

Export type:compileinfo 

type compileinfo is typedict:type2dict  
,code:seq.seq.symbolref,src:seq.seq.word
,symbolrefdecode:seq.symbol,mods:seq.libraryModule


   Function roots(s:compileinfo) set.symbol
   for acc= empty:set.symbol, m =mods.s do 
     if issimple.modname.m then  
     for acc2=acc, r=exports.m do  
     acc2+(symbolrefdecode.s)_toint.r 
     /for(acc2)
     else acc
    /for(acc)

Export code(compileinfo) seq.seq.symbolref

Export mods(compileinfo) seq.libraryModule


Export src(compileinfo) seq.seq.word

Function prg(s:compileinfo) seq.symdef 
let symdecode=symbolrefdecode.s
  for acc4=empty:seq.symdef, c=code.s do
      acc4+symdef(symdecode_toint.first.c,
          for   acc=empty:seq.symbol, r= c << 2 do   acc+ symdecode_toint.r /for(acc))
/for(acc4)

Export typedict(compileinfo) type2dict

Export symbolrefdecode(compileinfo) seq.symbol

Function alltypes(s:compileinfo) type2dict typedict.s

 
Function  compileinfo(prg:seq.symdef, alltypes:type2dict ,mods:seq.libraryModule
,src:seq.seq.word) compileinfo
compileinfo(alltypes, cvtL3(program.asset.prg,1,empty:seq.seq.symbolref),src,symbolrefdecode,mods)




Function cvtL2( alltypes: type2dict,prg:program,  mods:seq.libraryModule) compileinfo
compileinfo(alltypes, cvtL3(prg,1,empty:seq.seq.symbolref),empty:seq.seq.word,symbolrefdecode,mods)

Function addprg(cinfo:compileinfo,prg:program) compileinfo
  compileinfo(typedict.cinfo,cvtL3(prg,1,empty:seq.seq.symbolref)
  ,src.cinfo,symbolrefdecode,mods.cinfo) 

 function cvtL3(prg:program,i:int, in: seq.seq.symbolref) seq.seq.symbolref
 let x=encoding:seq.encodingpair.symbol
 if i > length.x then in 
 else 
    cvtL3(prg,length.x+1, 
       for acc=in , p=subseq(x,i,length.x)   do
         let f=findelement(symdef(data.p,empty:seq.symbol),data.prg)
         if isempty.f /or isempty.code.f_1 then  acc   
         else 
               acc+for acc2 = [ symbolref.data.p,symbolref.Lit.paragraphno.f_1], sym = code.f_1  do 
                       acc2+if isFref.sym then
                        let  discard=symbolref.basesym.sym
                        symbolref.sym 
                       else if  isrecordconstant.sym then
                        let discard= for acc3=symbolref.Lit.0 ,  sym2=removeconstant.[sym] do symbolref.sym2 /for(acc3)
                        symbolref.sym
                       else 
                        symbolref.sym /for(acc2)
                    /for(acc))
  


use set.word
  
Function addoption(p:program, s:symbol, option:seq.word)program
{ must maintain library of symbol in p}
 let f=findelement(symdef(s,empty:seq.symbol),data.p)
  let code= if isempty.f then empty:seq.symbol else code.f_1
let current = asset.getoption.code
 if current = asset.option then p
 else
  let newcode = removeoptions.code + Words.toseq(current ∪ asset.option) + Optionsym
   map(p, if isempty.f then s else sym.f_1, newcode)



Module codetemplates

use bits

use fileio

use internalbc

use llvm

use llvmconstants

use mangle

use persistant

use standard

use symbol

use program

use textio

use seq.bit

use set.int

use otherseq.llvmtype

use seq.llvmtype

use encoding.match5

use seq.match5

use seq.mytype

use set.mytype

use seq.symbol

use set.symbol

use seq.seq.int

use seq.seq.symbol

Export constdata seq.slot

Export wordref(w:word)int

Export addliblib(libname:seq.word, mods:seq.int, profiledata:int, isbase:boolean)int

function tollvmtype(alltypes:type2dict, s:symbol)llvmtype
 if s = Optionsym then function.[ i64, i64, i64, i64]else function.tollvmtypelist(alltypes, s)
 
function tollvmtypelist(alltypes:type2dict, s:symbol)seq.llvmtype
 assert resulttype.s ≠ typeT report"TTT" + print.s
let starttypes = [ tollvmtype(alltypes, resulttype.s), i64]
for acc = starttypes, @e = paratypes.s do 
   assert @e ≠ typeT report"TTTP" + print.s
    acc + tollvmtype(alltypes, @e)
  /for(acc)

function tollvmtype(alltypes:type2dict, s:mytype)llvmtype
 if isseq.s then ptr.i64
 else if abstracttypename.s="process"_1 then ptr.i64
 else
  let kind = coretype(s,alltypes )
  if kind = typeint ∨ kind = typeboolean then i64
   else if kind = typereal then double else ptr.i64

Function conststype llvmtype array(-2, i64)

Function profiletype llvmtype array(-3, i64)

Export type:match5

Export length(match5)int { no of instruction that return results }

Export action(match5)word

Export arg(match5)int

Function firstvar(a:match5)int length.a

Function brt(a:match5)int length.a

Function brf(a:match5)int arg.a

Export llvmtypelist(match5)seq.llvmtype

type match5 is sym:symbol, length:int, parts:internalbc, action:word, arg:int, code:seq.symbol, llvmtypelist:seq.llvmtype

Function functype(m:match5)llvmtype function.llvmtypelist.m

function addtemplate(sym:symbol, length:int, parts:internalbc, action:word, arg:int, code:seq.symbol, llvmtypelist:seq.llvmtype)match5
let m = match5(sym, length, parts, action, arg, code, llvmtypelist)
let discard = encode.m
 m

function addtemplate(sym:symbol, length:int, parts:internalbc, action:word, arg:slot)match5
 addtemplate(sym, length, parts, action, toint.arg, empty:seq.symbol, [ i64])

function addtemplate(sym:symbol, length:int, b:internalbc)match5 addtemplate(sym, length, b,"TEMPLATE"_1, slot.nopara.sym)

function addtemplates(t:seq.word, sym:symbol, length:int, b:internalbc)match5
 first.for acc = empty:seq.match5, e = t do
  [ addtemplate(replaceTsymbol(typeref([ e] + "? ?"), sym), length, b)]
 /for(acc)

function findtemplate(d:symbol)seq.match5 findencode.match5(d, 0, emptyinternalbc,"NOTFOUND"_1, 0, empty:seq.symbol, [ i64])

Export code(match5)seq.symbol

Export type:symbol

Function_(m:seq.match5, d:symbol)match5
let e = findtemplate.d
 assert not.isempty.e report"LL codetemplates" + print.d + stacktrace
  e_1

function =(a:match5, b:match5)boolean sym.a = sym.b

function hash(a:match5)int fsighash.sym.a

function assignencoding(p:seq.encodingpair.match5, a:match5)int length.p + 1

Function options(match5map:seq.match5, m:match5)seq.word getoption.code.m

Function funcdec(alltypes:type2dict, i:symbol)int
 toint.modulerecord([ mangledname.i], [ toint.FUNCTIONDEC, typ.tollvmtype( alltypes, i), 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])

Function match5map(theprg:program, uses:set.symbol, alltypes:type2dict)seq.match5
let discard3 = [ addtemplate(symbol(internalmod,"packedindex", seqof.typebit, typeint, typeint), 8, BINOP(r.1, ibcsub.2, C64.1, sub) + BINOP(r.2, r.1, C64.6, lshr)
+ BINOP(r.3, r.2, C64.2, add)
+ GEP(r.4, i64, ibcsub.1, r.3)
+ LOAD(r.5, r.4, i64)
+ BINOP(r.6, r.1, C64.63, and)
+ BINOP(r.7, r.5, r.6, lshr)
+ BINOP(r.8, r.7, C64.1, and))
, addtemplate(symbol(internalmod,"packedindex", seqof.typebyte, typeint, typeint), 9, BINOP(r.1, ibcsub.2, C64.1, sub) + BINOP(r.2, r.1, C64.3, lshr)
+ BINOP(r.3, r.2, C64.2, add)
+ GEP(r.4, i64, ibcsub.1, r.3)
+ LOAD(r.5, r.4, i64)
+ BINOP(r.6, r.1, C64.7, and)
+ BINOP(r.7, r.6, C64.3, shl)
+ BINOP(r.8, r.5, r.7, lshr)
+ BINOP(r.9, r.8, C64.255, and))
, addtemplate(symbol(internalmod,"packedindex", seqof.typeref."packed2 tausupport.", typeint, typeptr), 4, BINOP(r.1, ibcsub.2, C64.-1, add) + BINOP(r.2, r.1, C64.2, mul)
+ BINOP(r.3, r.2, C64.2, add)
+ GEP(r.4, i64, ibcsub.1, r.3))
, addtemplate(symbol(internalmod,"packedindex", seqof.typeref."packed3 tausupport.", typeint, typeptr), 4, BINOP(r.1, ibcsub.2, C64.-1, add) + BINOP(r.2, r.1, C64.3, mul)
+ BINOP(r.3, r.2, C64.2, add)
+ GEP(r.4, i64, ibcsub.1, r.3))
, addtemplate(symbol(internalmod,"packedindex", seqof.typeref."packed4 tausupport.", typeint, typeptr), 4, BINOP(r.1, ibcsub.2, C64.-1, add) + BINOP(r.2, r.1, C64.4, mul)
+ BINOP(r.3, r.2, C64.2, add)
+ GEP(r.4, i64, ibcsub.1, r.3))
, addtemplate(symbol(internalmod,"packedindex", seqof.typeref."packed5 tausupport.", typeint, typeptr), 4, BINOP(r.1, ibcsub.2, C64.-1, add) + BINOP(r.2, r.1, C64.5, mul)
+ BINOP(r.3, r.2, C64.2, add)
+ GEP(r.4, i64, ibcsub.1, r.3))
, addtemplate(symbol(internalmod,"packedindex", seqof.typeref."packed6 tausupport.", typeint, typeptr), 4, BINOP(r.1, ibcsub.2, C64.-1, add) + BINOP(r.2, r.1, C64.6, mul)
+ BINOP(r.3, r.2, C64.2, add)
+ GEP(r.4, i64, ibcsub.1, r.3))
, addtemplate(symbol(moduleref."fileio","tocstr", seqof.typebits, typeref."fileio cstr."), 2, GEP(r.1, i64, ibcsub.1, C64.2) + CAST(r.2, r.1, i64, ptrtoint))
, addtemplate(symbol(moduleref."bits","toint", typebyte, typeint), 0, emptyinternalbc)
, addtemplate(symbol(moduleref."bits","toint", typebit, typeint), 0, emptyinternalbc)
, { addtemplate(NullptrOp, 1, CAST(r.1, C64.0, ptr.i64, inttoptr)), addtemplate(STKRECORDOp, 3, ALLOCA(r.1, ptr.ptr.i64, i64, C64.2, 0)+ STORE(r.2, r.1, ibcsub.1)+ GEP(r.2, ptr.i64, r.1, C64.1)+ STORE(r.3, r.2, ibcsub.2)+ GEP(r.3, ptr.i64, r.1, C64.0)), addtemplate(symbol("bitcast(ptr)","builtin","int"), 1, CAST(r.1, ibcsub.1, i64, ptrtoint)), addtemplate(symbol("bitcast(int seq)","interpreter","int"), 1, CAST(r.1, ibcsub.1, i64, ptrtoint)), }
addtemplate(symbol(moduleref."interpreter","GEP", seqof.typeint, typeint, typeint), 2, GEP(r.1, i64, ibcsub.1, ibcsub.2) + CAST(r.2, r.1, i64, ptrtoint))
, addtemplate(symbol(moduleref."interpreter","bitcast", typeint, seqof.typeint), 1, CAST(r.1, ibcsub.1, ptr.i64, inttoptr))
, addtemplate(symbol(internalmod,"bitcast", typeptr, typeptr), 1, GEP(r.1, i64, ibcsub.1, C64.0))
, addtemplate(symbol4(moduleref."tausupport","toseqX"_1, seqof.typeint, [ typeptr], seqof.typeint), 0, emptyinternalbc)
, addtemplates("bit byte int ptr real packed2 packed3 packed4 packed5 packed6", symbol4(internalmod,"toseq"_1, seqof.typeT, [ typeptr], typeptr), 0, emptyinternalbc)
, addtemplate(symbol(moduleref."real","intpart", typereal, typeint), 1, CAST(r.1, ibcsub.1, i64, fptosi))
, addtemplate(symbol(moduleref."real","toreal", typeint, typereal), 1, CAST(r.1, ibcsub.1, double, sitofp))
, addtemplate(symbol(moduleref."real","-", typereal, typereal, typereal), 1, BINOP(r.1, ibcsub.1, ibcsub.2, sub))
, addtemplate(symbol(moduleref."real","+", typereal, typereal, typereal), 1, BINOP(r.1, ibcsub.1, ibcsub.2, add))
, addtemplate(symbol(moduleref."real","*", typereal, typereal, typereal), 1, BINOP(r.1, ibcsub.1, ibcsub.2, mul))
, addtemplate(symbol(moduleref."real","/", typereal, typereal, typereal), 1, BINOP(r.1, ibcsub.1, ibcsub.2, sdiv))
, addtemplate(symbol(moduleref."real","casttoreal", typeint, typereal), 1, CAST(r.1, ibcsub.1, double, bitcast))
, addtemplate(symbol(moduleref."real","representation", typereal, typeint), 1, CAST(r.1, ibcsub.1, i64, bitcast))
, addtemplate(symbol(moduleref."real","?", typereal, typereal, typeref."ordering standard."), 5, CMP2(r.1, ibcsub.1, ibcsub.2, 3) + CAST(r.2, r.1, i64, zext)
+ CMP2(r.3, ibcsub.1, ibcsub.2, 2)
+ CAST(r.4, r.3, i64, zext)
+ BINOP(r.5, r.2, r.4, add))
, addtemplate(symbol(moduleref."standard","?", typeint, typeint, typeref."ordering standard."), 5, CMP2(r.1, ibcsub.1, ibcsub.2, 39) + CAST(r.2, r.1, i64, zext)
+ CMP2(r.3, ibcsub.1, ibcsub.2, 38)
+ CAST(r.4, r.3, i64, zext)
+ BINOP(r.5, r.2, r.4, add))
, addtemplate(symbol(internalmod,"GEP", seqof.typeptr, typeint, typeptr), 1, GEP(r.1, i64, ibcsub.1, ibcsub.2))
, addtemplate(symbol(moduleref."standard","not", typeboolean, typeboolean), 1, BINOP(r.1, ibcsub.1, C64.1, xor))
, addtemplate(symbol(moduleref."standard",">", typeint, typeint, typeboolean), 2, CMP2(r.1, ibcsub.1, ibcsub.2, 38) + CAST(r.2, r.1, i64, zext))
, addtemplate(symbol(moduleref."standard","=", typeboolean, typeboolean, typeboolean), 2, CMP2(r.1, ibcsub.1, ibcsub.2, 32) + CAST(r.2, r.1, i64, zext))
, addtemplate(symbol(moduleref."standard","=", typeint, typeint, typeboolean), 2, CMP2(r.1, ibcsub.1, ibcsub.2, 32) + CAST(r.2, r.1, i64, zext))
, addtemplate(symbol(moduleref."standard","-", typeint, typeint, typeint), 1, BINOP(r.1, ibcsub.1, ibcsub.2, sub))
, addtemplate(symbol(moduleref."standard","+", typeint, typeint, typeint), 1, BINOP(r.1, ibcsub.1, ibcsub.2, add))
, addtemplate(symbol(moduleref."standard","*", typeint, typeint, typeint), 1, BINOP(r.1, ibcsub.1, ibcsub.2, mul))
, addtemplate(symbol(moduleref."standard","/", typeint, typeint, typeint), 1, BINOP(r.1, ibcsub.1, ibcsub.2, sdiv))
, addtemplate(symbol(moduleref."bits","<<", typebits, typeint, typebits), 1, BINOP(r.1, ibcsub.1, ibcsub.2, shl))
, addtemplate(symbol(moduleref."bits",">>", typebits, typeint, typebits), 1, BINOP(r.1, ibcsub.1, ibcsub.2, lshr))
, addtemplate(symbol(moduleref."bits","∧", typebits, typebits, typebits), 1, BINOP(r.1, ibcsub.1, ibcsub.2, and))
, addtemplate(symbol(moduleref."bits","∨", typebits, typebits, typebits), 1, BINOP(r.1, ibcsub.1, ibcsub.2, or))
, addtemplate(symbol(moduleref."bits","xor", typebits, typebits, typebits), 1, BINOP(r.1, ibcsub.1, ibcsub.2, xor))
, addtemplate(symbol(moduleref."tausupport","set", [ typeptr, typeint], typeptr), 1, STORE(r.1, ibcsub.1, ibcsub.2) + GEP(r.1, i64, ibcsub.1, C64.1))
, addtemplate(abortsymbol.typeint
, 1
, CALL(r.1, 0, 32768, function.[ i64, i64, ptr.i64], symboltableentry("assert", function.[ i64, i64, ptr.i64]), slot.ibcfirstpara2, ibcsub.1)
)
, addtemplate(abortsymbol.typeboolean
, 1
, CALL(r.1, 0, 32768, function.[ i64, i64, ptr.i64], symboltableentry("assert", function.[ i64, i64, ptr.i64]), slot.ibcfirstpara2, ibcsub.1)
)
, addtemplate(abortsymbol.typereal
, 2
, CALL(r.1, 0, 32768, function.[ i64, i64, ptr.i64], symboltableentry("assert", function.[ i64, i64, ptr.i64]), slot.ibcfirstpara2, ibcsub.1)
+ CAST(r.2, r.1, double, sitofp)
)
, addtemplate(abortsymbol.typeptr
, 2
, CALL(r.1, 0, 32768, function.[ i64, i64, ptr.i64], symboltableentry("assert", function.[ i64, i64, ptr.i64]), slot.ibcfirstpara2, ibcsub.1)
+ CAST(r.2, r.1, ptr.i64, inttoptr)
)
, addtemplates("int boolean bit byte", symbol(internalmod,"callidx", seqof.typeT, typeint, typeint), 4, GEP(r.1, i64, ibcsub.1, C64.0) + LOAD(r.2, r.1, i64)
+ CAST(r.3, r.2, ptr.function.[ i64, i64, ptr.i64, i64], inttoptr)
+ CALL(r.4, 0, 32768, function.[ i64, i64, ptr.i64, i64], r.3, slot.ibcfirstpara2, ibcsub.1, ibcsub.2))
, addtemplate(symbol(internalmod,"callidx", seqof.typereal, typeint, typereal), 4, GEP(r.1, i64, ibcsub.1, C64.0) + LOAD(r.2, r.1, i64)
+ CAST(r.3, r.2, ptr.function.[ double, i64, ptr.i64, i64], inttoptr)
+ CALL(r.4, 0, 32768, function.[ double, i64, ptr.i64, i64], r.3, slot.ibcfirstpara2, [ ibcsub.1, ibcsub.2]))
, addtemplates("ptr packed2 packed3 packed4 packed5 packed6"
, symbol(internalmod,"callidx", seqof.typeT, typeint, typeptr)
, 4
, GEP(r.1, i64, ibcsub.1, C64.0) + LOAD(r.2, r.1, i64)
+ CAST(r.3, r.2, ptr.function.[ ptr.i64, i64, ptr.i64, i64], inttoptr)
+ CALL(r.4, 0, 32768, function.[ ptr.i64, i64, ptr.i64, i64], r.3, slot.ibcfirstpara2, [ ibcsub.1, ibcsub.2])
)
, addtemplates("int boolean byte bit", symbol(internalmod,"idxseq", seqof.typeT, typeint, typeint), 3, BINOP(r.1, ibcsub.2, C64.1, add) + GEP(r.2, i64, ibcsub.1, r.1)
+ LOAD(r.3, r.2, i64))
, addtemplate(symbol(internalmod,"idxseq", seqof.typereal, typeint, typereal), 4, BINOP(r.1, ibcsub.2, C64.1, add) + GEP(r.2, i64, ibcsub.1, r.1)
+ LOAD(r.3, r.2, i64)
+ CAST(r.4, r.3, double, bitcast))
, addtemplates("ptr packed2 packed3 packed4 packed5 packed6", symbol(internalmod,"idxseq", seqof.typeT, typeint, typeptr), 4, BINOP(r.1, ibcsub.2, C64.1, add) + GEP(r.2, i64, ibcsub.1, r.1)
+ LOAD(r.3, r.2, i64)
+ CAST(r.4, r.3, ptr.i64, inttoptr))
, addtemplate(GetSeqLength, 2, GEP(r.1, i64, ibcsub.1, C64.1) + LOAD(r.2, r.1, i64))
, addtemplate(GetSeqType, 1, LOAD(r.1, ibcsub.1, i64))
, addtemplate(symbol(moduleref("builtin", typeint),"load", [ typeptr, typeint], typeint), 2, GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64))
, addtemplate(symbol(moduleref("builtin", typeboolean),"load", [ typeptr, typeint], typeboolean), 2, GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64))
, addtemplate(symbol(moduleref("builtin", typeptr),"load", [ typeptr, typeint], typeptr), 3, GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64)
+ CAST(r.3, r.2, ptr.i64, inttoptr))
, addtemplate(symbol(moduleref("builtin", typereal),"load", [ typeptr, typeint], typereal), 3, GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64)
+ CAST(r.3, r.2, double, bitcast))
, addtemplate(symbol(moduleref("builtin", typeint),"fld", [ typeptr, typeint], typeint), 2, GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64))
, addtemplate(symbol(moduleref("builtin", typeboolean),"fld", [ typeptr, typeint], typeboolean), 2, GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64))
, addtemplate(symbol(moduleref("builtin", typeptr),"fld", [ typeptr, typeint], typeptr), 3, GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64)
+ CAST(r.3, r.2, ptr.i64, inttoptr))
, addtemplate(symbol(moduleref("builtin", typereal),"fld", [ typeptr, typeint], typereal), 3, GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64)
+ CAST(r.3, r.2, double, bitcast))
]
let const = for acc = empty:seq.symbol, e = toseq(uses - asset.[ Optionsym])do
 if isconst.e then
  if isrecordconstant.e then acc + e
  else { let discard = buildrecordconst(e, alltypes)acc else }let discard = buildconst(e, alltypes)
  acc
 else let discard5 = buildtemplate(theprg, alltypes, e)
 acc
/for(acc)
let discard4 = processconst.const
 empty:seq.match5


Function symboltableentry(name:seq.word, type:llvmtype)slot
 modulerecord(name, [ toint.FUNCTIONDEC, typ.type, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])

function processconst(toprocess:seq.symbol)int
 if isempty.toprocess then 0
 else
  processconst.for notprocessed = empty:seq.symbol, xx = toprocess do
   for args = empty:seq.int, defined = true, ele = constantcode.xx while defined do let tp = findtemplate.ele
    if isempty.tp then next(empty:seq.int, false)else next(args + arg.tp_1, true)/for(if defined then
   let discard = addtemplate(xx, 0, emptyinternalbc,"ACTARG"_1, slot.addobject.args)
   notprocessed
   else notprocessed + xx /if)
  /for(notprocessed)


function =(a:llvmtype, b:llvmtype)boolean typ.a = typ.b

function buildconst(xx:symbol, alltypes:type2dict)match5
 if isFref.xx then
 let f1 =(constantcode.xx)_1
 let mn = mangledname.f1
 let functyp = ptr.tollvmtype(alltypes, f1)
 addtemplate(xx, 0, emptyinternalbc,"ACTARG"_1, ptrtoint(functyp, symboltableentry([mn], functyp)))
 else if inmodule(xx,"$real")then addtemplate(xx, 0, emptyinternalbc,"ACTARG"_1, Creal.value.xx)
 else if inmodule(xx,"$int")then addtemplate(xx, 0, emptyinternalbc,"ACTARG"_1, C64.value.xx)
 else if iswordseq.xx then addtemplate(xx, 0, emptyinternalbc,"ACTARG"_1, slot.addwordseq2.worddata.xx)
 else if xx = Littrue then addtemplate(xx, 0, emptyinternalbc,"ACTARG"_1, C64.1)
 else if xx = Litfalse then addtemplate(xx, 0, emptyinternalbc,"ACTARG"_1, C64.0)
 else
  assert isword.xx report"not a constant" + print.xx
   addtemplate(xx, 0, emptyinternalbc,"ACTARG"_1, slot.wordref.wordname.xx)

function buildtemplate(theprg:program, alltypes:type2dict, xx:symbol)match5
 { xx will not be constant }
 if islocal.xx then addtemplate(xx, 0, emptyinternalbc,"LOCAL"_1, slot.value.xx)
 else if isdefine.xx then addtemplate(xx, 0, emptyinternalbc,"DEFINE"_1, slot.value.xx)
 else if isblock.xx then addtemplate(xx, 0, emptyinternalbc, wordname.xx, 0, empty:seq.symbol, [ i64])
 else if isstart.xx then
 let typ = tollvmtype(alltypes, resulttype.xx)
 addtemplate(xx, 0, emptyinternalbc, wordname.xx, nopara.xx, empty:seq.symbol, [ typ])
 else if isspecial.xx then
  if isRecord.xx then
   if nopara.xx < 10 then
   let fldbc = recordcode(arithseq(nopara.xx, 1, ibcfirstpara2 + 1), tollvmtypelist(alltypes, xx) << 2, 0, true)
   addtemplate(xx, regno.fldbc, bc.fldbc)
   else addtemplate(xx, 0, emptyinternalbc, wordname.xx, nopara.xx, empty:seq.symbol, tollvmtypelist(alltypes, xx) << 2)
  else if isSequence.xx then
   if nopara.xx < 10 then
   let fldbc = sequencecode(arithseq(nopara.xx, 1, ibcfirstpara2 + 1), tollvmtype(alltypes, para.module.xx), 0, true)
   addtemplate(xx, regno.fldbc, bc.fldbc)
   else
    addtemplate(xx, 0, emptyinternalbc,"SEQUENCE"_1, nopara.xx, empty:seq.symbol, [ tollvmtype(alltypes, para.module.xx)])
  else if isbr.xx then addtemplate(xx, brt.xx, emptyinternalbc, wordname.xx, brf.xx, empty:seq.symbol, [ i64])
  else if isloopblock.xx then
   addtemplate(xx, firstvar.xx, emptyinternalbc, wordname.xx, nopara.xx, empty:seq.symbol, for oldacc = [ tollvmtype(alltypes, resulttype.xx)], e20 = paratypes.xx do oldacc + tollvmtype(alltypes, e20)/for(oldacc))
  else if iscontinue.xx then addtemplate(xx, 0, emptyinternalbc,"CONTINUE"_1, nopara.xx, empty:seq.symbol, [ i64])
  else addtemplate(xx, 0, emptyinternalbc, wordname.xx, nopara.xx, empty:seq.symbol, [ i64])
 else
  { handle builtin package }
  let intable = findtemplate.xx
   if length.intable > 0 then intable_1
   else if wordname.xx = "global"_1 ∧ inmodule(xx,"$global")then
    addtemplate(xx, 1, GEP(r.1, i64, slot.global([ mangledname.xx], i64, C64.0)))
   else if wordname.xx = "createthreadY"_1 ∧ inmodule(xx,"builtin")then
   let l = for acc = empty:seq.llvmtype, e = paratypes.xx << 3 do acc + tollvmtype(alltypes, e)/for(acc + tollvmtype(alltypes, para.module.xx))
   assert true report"TTT" + print.xx
    + for ll ="", e = l do ll + print.e /for(ll)
    addtemplate(xx, 0, emptyinternalbc, wordname.xx, nopara.xx, empty:seq.symbol, l)
   else call(alltypes, xx,"CALL"_1, getCode(theprg, xx), mangledname.xx)

function call(alltypes:type2dict, xx:symbol, type:word, code:seq.symbol, symname:word)match5
let list = tollvmtypelist(alltypes, xx)
let functype = function.list
let newcode = CALLSTART(1, 0, 32768, typ.functype, toint.symboltableentry([symname], functype), if type = "CALL"_1 then nopara.xx + 1 else nopara.xx)
addtemplate(xx, 1, newcode, type, nopara.xx, code, list)

Function usetemplate(t:match5, deltaoffset:int, argstack:seq.int)internalbc
let args = if action.t = "CALL"_1 then empty:seq.int
else subseq(argstack, length.argstack - arg.t + 1, length.argstack)
processtemplate(parts.t, deltaoffset, args)

type recordcoderesult is regno:int, bc:internalbc

Export regno(recordcoderesult)int

Export bc(recordcoderesult)internalbc

Export type:recordcoderesult

function setnextfld(bc:internalbc, args:seq.int, i:int, types:seq.llvmtype, regno:int, pint:int, preal:int, pptr:int)recordcoderesult
 if i > length.args then recordcoderesult(regno, bc)
 else
  let typ = types_i
   if typ = double then
    if preal = 0 then
     setnextfld(bc + CAST(r(regno + 1), r.pint, ptr.double, bitcast), args, i, types, regno + 1, pint, regno + 1, pptr)
    else
     let newbc = GEP(r(regno + 1), double, r.preal, C64(i - 1))
     + STORE(r(regno + 2), r(regno + 1), slot.args_i)
     setnextfld(bc + newbc, args, i + 1, types, regno + 1, pint, preal, pptr)
   else if typ = ptr.i64 then
    if pptr = 0 then
     setnextfld(bc + CAST(r(regno + 1), r.pint, ptr.ptr.i64, bitcast), args, i, types, regno + 1, pint, preal, regno + 1)
    else
     let newbc = GEP(r(regno + 1), ptr.i64, r.pptr, C64(i - 1))
     + STORE(r(regno + 2), r(regno + 1), slot.args_i)
     setnextfld(bc + newbc, args, i + 1, types, regno + 1, pint, preal, pptr)
   else
    let newbc = GEP(r(regno + 1), i64, r.pint, C64(i - 1))
    + STORE(r(regno + 2), r(regno + 1), slot.args_i)
    setnextfld(bc + newbc, args, i + 1, types, regno + 1, pint, preal, pptr)

Function sequencecode(args:seq.int, type:llvmtype, lastreg:int, template:boolean)recordcoderesult
 recordcode([ toint.C64.0, toint.C64.length.args] + args, [ i64, i64] + constantseq(length.args, type), lastreg, template)

Function recordcode(args:seq.int, types:seq.llvmtype, lastreg:int, template:boolean)recordcoderesult
let firstpara = if template then slot.ibcfirstpara2 else r.1
let newcode = CALL(r(lastreg + 1), 0, 32768, function.[ ptr.i64, i64, i64], symboltableentry("allocatespace", function.[ ptr.i64, i64, i64]), firstpara, C64.length.args)
let c = setnextfld(newcode, args, 1, types, lastreg + 1, lastreg + 1, 0, 0)
if template then
  recordcoderesult(regno.c + 1, bc.c + GEP(r(regno.c + 1), i64, r(lastreg + 1), C64.0))
 else c 