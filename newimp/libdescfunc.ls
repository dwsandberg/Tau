#!/usr/local/bin/tau

module libdescfunc

run newimp test1

use stdlib

use libscope

use cvttoinst

use borrow2

use set.word

use set.int

use seq.int

use seq.inst

use seq.seq.int

use seq.libsym

use other

use seq.libmod

use set.libsym

use set.symbol

use seq.libtype

use Symbol

use seq.firstpass

Function libdesc(roots:set.word,intercode:intercode2,lib:word,mods:seq.firstpass,known:symbolset)liblib 
  let rootindices = asset.@(+, toinstindex(roots, intercode), empty:seq.int, defines.intercode)
   let a = close(intercode, rootindices, rootindices)
   let syms = @(+, tolibsym(intercode), empty:seq.libsym, toseq.a)
   let allmods = @(map(lib,known), identity,mapresult(asset.syms,empty:seq.libmod), mods)
  liblib([lib],  empty:seq.libtype , mods.allmods+libmod(false,"$other"_1, toseq.syms.allmods, empty:seq.libsym, lib))

  @(+, print,"",toseq.asset.@(+, exports,  empty:seq.libsym ,allmods))

    
  
  function toinstindex(a:set.word, d:intercode2, i:int)seq.int 
 if mangledname(coding(d)_i)in a then [ i]else empty:seq.int

function close(d:intercode2, toprocess:set.int, old:set.int)set.int 
 let a = asset.@(+, simpleonly.d, empty:seq.int, toseq.toprocess) - old 
  let new = asset.@(+, filter.d, empty:seq.int, toseq.a) - old 
  if isempty.new then old else close(d, new, old ∪ new)

function simpleonly(d:intercode2, i:int)seq.int 
  // returns body for simple function otherwise and empty sequence //
 let body = codes(d)_i
  if length.body > 30  then   empty:seq.int
  else 
   let flags=flags.(coding.d)_i
   if    ("SIMPLE"_1 in flags &or  "INLINE"_1 in flags)  then body else empty:seq.int
  
function filter(d:intercode2, i:int)seq.int 
 let inst = coding(d)_i 
  let name = mangledname.inst 
  if name in"SET WORD WORDS DEFINE LOCAL LIT PARAM IDXUC LIT ELSEBLOCK RECORD THENBLOCK if CONTINUE LOOPBLOCK FINISHLOOP FIRSTVAR"
  then empty:seq.int 
  else if name in"CONSTANT FREF"
  then let a = if name ="CONSTANT"_1 
    then asset.findcalls(towords.inst, 2,"")
    else asset.[ towords(inst)_2]
   if isempty.a 
   then empty:seq.int 
   else let result = @(+, toinstindex(a, d), empty:seq.int, arithseq(length.coding.d, 1, 1))
   assert length.toseq.a = length.result report"Did not find all function embedded in CONSTANT"+ toseq.a 
   result 
  else [ i]
  
  function findcalls(a:seq.word, i:int, result:seq.word)seq.word 
 if i > length.a 
  then result 
  else findcalls(a, i + 2, result + if a_i ="FREF"_1 then [ a_(i + 1)]else"")


function astext(s:seq.inst, i:int)seq.word 
 let f = towords(s_i)
  if f_1 ="CONSTANT"_1 
  then subseq(f, 2, length.f)
  else if f_1 ="PARAM"_1 then"PARAM"+ toword(-toint(f_2)- 1)else 
  if f_1 in "ELSEBLOCK THENBLOCK DEFINE" then ""
  else 
  if f_1 in"SET WORD WORDS LOCAL LIT PARAM  RECORD FREF" then f
  else [f_1]
 

function astext5( s:seq.inst, d:seq.int)seq.word @(+, astext( s),"", d)

function tolibsym(d:intercode2, i:int)seq.libsym 
  let a = (coding.d)_i 
  if mangledname.a in"CONSTANT EQL RECORD"∨"builtin"_1 in flags.a 
  then empty:seq.libsym 
  else let inst = if"STATE"_1 in flags.a 
   then [ mangledname.a,"STATE"_1,"1"_1]
   else 
     let body=simpleonly(d,i)
    if length.body > 0  
     then 
       // assert mangledname.a &ne "arithseqZintzseqZintZTZT"_1 report astext5(coding.d, (codes.d)_i) //
     astext5(coding.d, (codes.d)_i)+flags.a  
   else "EXTERNAL"
  [ libsym(returntype.a, mangledname.a, inst)]
  

type mapresult is record syms:set.libsym,mods:seq.libmod

type mapresult2 is record syms:set.libsym,libsyms:seq.libsym

use seq.symbol

function map(lib:word,known:symbolset,r:mapresult,l:firstpass) mapresult
 if not.exportmodule.l  
  then r
  else if isabstract.modname.l 
  then mapresult(syms.r, mods.r+libmod(true, abstracttype.modname.l, @(+, tolibsym4, empty:seq.libsym, toseq.defines.l),
     @(+, tolibsym4, empty:seq.libsym, toseq.exports.l), lib))
  else 
     // let d=@(findelement.known,identity, mapresult2(syms.r,empty:seq.libsym), toseq.defines.l)//
     let e= @(findelement.known,identity, mapresult2(syms.r,empty:seq.libsym), toseq.exports.l)
    mapresult(syms.e, mods.r+libmod(false, abstracttype.modname.l,  empty:seq.libsym,libsyms.e, lib))

function tolibsym4(s:symbol)libsym 
  libsym(resulttype.s, mangledname.s, src.s) 

function findelement(syms:set.libsym, s:symbol)seq.libsym 
 toseq.findelement(libsym(resulttype.s, mangledname.s, ""), syms)
 
function findelement(known:symbolset,r:mapresult2,s:symbol) mapresult2
   let z=findelement(libsym(resulttype.s, mangledname.s, ""), syms.r)
    if isempty.z then
        let t1=known_mangledname.s 
        let t=tolibsym4.t1
        assert src.t1 in ["EXTERNAL","xPARAM 1 VERYSIMPLE" ] report print2.t1
        mapresult2(syms.r+t,libsyms.r+t)
    else mapresult2(syms.r,libsyms.r+z_1)
        
 
 function ?(a:libsym, b:libsym)ordering fsig.a ? fsig.b


/type libsym is record fsig:word, returntype:seq.word, instruction:seq.word

use seq.mytype



Function tosymbol(ls:libsym) symbol
let d=codedown(fsig.ls)
symbol(d_1_1,mytype(d_2),@(+,mytype,empty:seq.mytype,subseq(d,3,length.d)),mytype.returntype.ls,instruction.ls)

Function tofirstpass(m:libmod) firstpass 
 firstpass(mytype.if parameterized.m then  "T"+modname.m else [modname.m],empty:seq.mytype,
  @(+,tosymbol,empty:set.symbol,defines.m),  @(+,tosymbol,empty:set.symbol,exports.m),empty:seq.symbol,empty:set.symbol,false)
  
Function tofirstpass(l:liblib) seq.firstpass
@(+,tofirstpass,empty:seq.firstpass,mods.l)

/type liblib is record libname:seq.word, types:seq.libtype, mods:seq.libmod, timestamp:int, readonly:boolean
/type libmod is record parameterized:boolean, modname:word, defines:seq.libsym, exports:seq.libsym, library:word
/type firstpass is record modname:mytype, uses:seq.mytype,defines:set.symbol,exports:set.symbol,unboundexports:seq.symbol,
unbound:set.symbol,exportmodule:boolean

 