module libdescfunc

use newsymbol

use libscope

use intercode

use seq.firstpass

use seq.inst

use seq.int

use seq.libmod

use seq.libsym

use seq.libtype

use seq.mytype

use seq.seq.int

use seq.symbol

use set.int

use set.libsym

use set.mytype

use set.symbol

use set.word

use stdlib
 
use convertlibtyp


function tolibsym(s:symbol) libsym  libsym(resulttype.s,mangledname.s,src.s)

Function libdesc(roots:set.word,intercode:intercode,mods:seq.firstpass,known:symbolset) seq.libmod
  let rootindices = asset.@(+, toinstindex(roots, intercode), empty:seq.int, defines.intercode)
  let a = close(intercode, rootindices, rootindices)
  let syms = @(+, tolibsym.intercode, empty:seq.libsym, toseq.a)
   let allmods  = @(map(known), identity, mapresult(asset.syms, empty:seq.libmod), mods)
  let typesyms=@(+,mytypetolibsym.known,empty:seq.libsym     ,toseq.asset.@(+,usestypes,empty:seq.mytype,mods.allmods))
   mods.allmods+ libmod(false,"$other"_1,  syms+typesyms ,empty:seq.libsym) 
  

 Function mytypetolibsym(s:symbolset,t:mytype) libsym
 // let x=findelement(symbol(merge("typedesc:"+ print.t), mytype."internal", empty:seq.mytype, mytype."word seq", ""),s)
  assert not.isempty.x report "unknown type?"+print.t 
  let a =x_1 //
  let a=  s_mangle(merge("typedesc:"+ print.t),mytype."internal", empty:seq.mytype)
  assert isdefined.a report "unknown type?"+print.t 
  libsym(resulttype.a, mangledname.a, src.a)
  
function usestypes(s:libmod) seq.mytype
 @(+,usestypes,empty:seq.mytype,exports.s)+@(+,usestypes,empty:seq.mytype,defines.s)


function usestypes(s:libsym) seq.mytype
 let d=codedown.fsig.s
   let x=  @(+,mytype,[mytype.returntype.s], subseq(d,3,length.d))
   @(+,primtypes,empty:seq.mytype,x)
     
function primtypes(m:mytype) seq.mytype
   let s = towords.m
   if length.s=1 then [m] else
     @(+,mytype,empty:seq.mytype,@( +, +."T",[[s_1]],subseq(s,2,length.s)))

   
function toinstindex(a:set.word, d:intercode, i:int)seq.int 
 if mangledname(coding(d)_i)in a then [ i]else empty:seq.int

function close(d:intercode, toprocess:set.int, old:set.int)set.int 
 let a = asset.@(+, simpleonly.d, empty:seq.int, toseq.toprocess) - old 
  let new = asset.@(+, filter.d, empty:seq.int, toseq.a) - old 
  if isempty.new then old else close(d, new, old ∪ new)

function simpleonly(d:intercode, i:int)seq.int 
 // returns body for simple function otherwise and empty sequence // 
  let body = codes(d)_i 
  if length.body > 10 
  then empty:seq.int 
  else let flags = flags(coding(d)_i)
  if"SIMPLE"_1 in flags ∨"INLINE"_1 in flags 
  then body 
  else empty:seq.int

function filter(d:intercode, i:int)seq.int 
 let inst = coding(d)_i 
  let name = mangledname.inst 
  if name in"SET WORD WORDS DEFINE LOCAL LIT PARAM IDXUC LIT ELSEBLOCK RECORD THENBLOCK if"
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
  else if f_1 ="PARAM"_1 
  then"PARAM"+ toword(-toint(f_2) - 1)
  else if f_1 in"ELSEBLOCK THENBLOCK DEFINE"
  then""
  else f

function astext5(s:seq.inst, d:seq.int)seq.word @(+, astext.s,"", d)

function tolibsym(d:intercode, i:int)seq.libsym 
  let a = coding(d)_i 
  if mangledname.a in"CONSTANT EQL RECORD"∨"builtin"_1 in flags.a 
  then empty:seq.libsym 
  else let inst = if"STATE"_1 in flags.a 
   then [ mangledname.a, toword.nopara.a,"STATE"_1,"1"_1]
   else let body = simpleonly(d, i)
  if length.body > 0 
  then  "USECALL"+ astext5(coding.d, codes(d)_i)
    else [ mangledname.a, toword.nopara.a]
  [ libsym(returntype.a, mangledname.a, inst)]

type mapresult is record syms:set.libsym, mods:seq.libmod

type mapresult2 is record syms:set.libsym, libsyms:seq.libsym

function map(known:symbolset, r:mapresult, l:firstpass)mapresult 
 if not.exportmodule.l 
  then r 
  else if isabstract.modname.l 
  then mapresult(syms.r, mods.r + libmod(true, abstracttype.modname.l, 
  @(+, tolibsym4, empty:seq.libsym, toseq.defines.l), @(+, tolibsym4, empty:seq.libsym, toseq.exports.l)))
  else 
   let d = @(findelement.known, identity, mapresult2(syms.r, empty:seq.libsym), toseq.exports.l)
   let e = @(findelement.known, identity, mapresult2(syms.d, empty:seq.libsym), toseq.exports.l)
  mapresult(syms.e, mods.r + libmod(false, abstracttype.modname.l, libsyms.d, libsyms.e))


function tolibsym4(s:symbol)libsym libsym(resulttype.s, mangledname.s, src.s)
  
function findelement(known:symbolset, r:mapresult2, s:symbol)mapresult2 
  let z = findelement(libsym(resulttype.s, mangledname.s,""), syms.r)
  if isempty.z 
  then // let t1 = known_mangledname.s 
   let t = tolibsym4.t1 
   assert src.t1 in ["EXTERNAL"]report "ERR33"+ print2.t1 
   mapresult2(syms.r + t, libsyms.r + t) //
    r
  else   mapresult2(syms.r, libsyms.r + z_1)


 



