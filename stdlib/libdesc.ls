

Module libdesc

use stdlib

use symbol

use seq.firstpass

use seq.inst

use seq.seq.int

use intercode

use libscope

use seq.seq.word

use seq.word

use seq.symbol

use set.symbol

use set.word

use seq.int

use seq.libsym

use worddict.libsym

use otherseq.libsym


Function libdesc(intercode:intercode, mods:seq.firstpass, known:symbolset)seq.libmod
  let abstract=@(+,abstractmods(coding.intercode,known),empty:seq.libmod,mods)
  let t=@(&cup,getmore,empty:set.symbol,mods)
  let b=@(+,find2(coding.intercode,known),empty:seq.libsym,toseq.t)
    let have=@(+,fsig,empty:set.word,b)
  let d=close(intercode,known,b,have,empty:seq.libsym)
  let z=@(add,identity,emptyworddict:worddict.libsym,d)
  @(+,libmod(z),abstract,mods)
+ libmod(false,"$other"_1, sort.d, empty:seq.libsym, empty:seq.mytype)

function  abstractmods(coding:seq.inst, known:symbolset,f:firstpass) seq.libmod
  if not.exportmodule.f &or not.isabstract.modname.f then empty:seq.libmod
  else  
    let d=sort.@(+,aslibsym.known,empty:seq.libsym,toseq.defines.f)
        let e=sort.@(+,aslibsym.known,empty:seq.libsym,toseq.exports.f)
    [libmod(true, abstracttype.modname.f,d,e, uses.f)]
    
function aslibsym(known:symbolset,sym1:symbol) libsym  
let sym2=lookupsymbol(known,mangledname.sym1)
let sym=if isdefined.sym2 then sym2 else 
assert src.sym1="STUB" report print2.sym1 sym1
libsym(resulttype.sym,mangledname.sym,stripparsedfunc.src.sym )
     
  
function getmore(f:firstpass) set.symbol
   if not.exportmodule.f &or isabstract.modname.f then empty:set.symbol
  else  
    exports.f
    
   

      
function filter(  i:int,result:seq.word, src:seq.word) seq.word
 if i > length.src then result
  else
  let name = src_i
   if name in "builtinZinternal1Zwordzseq builtinZinternal1Zinternal1 if  IDXUC getinstanceZbuiltinZTzerecord
   STATEZinternal1Zinternal1" then filter( i + 1,result, src)
   else if name in "SET LIT PARAM LOCAL WORD DEFINE
    RECORD APPLY LOOPBLOCK  CONTINUE FINISHLOOP CRECORD BLOCK EXITBLOCK BR" then filter( i + 2, result,src)
   else if name = "FREF"_1 then filter( i+2,result+src_(i+1),src)
   else  if name = "WORDS COMMENT"_1 then
   filter( i + toint.src_(i + 1) + 2,result, src)
   else  filter( i+1, result+name,src)
     
 function calls(a:libsym) seq.word   
   let d= codedown.fsig.a
   if (d_2)_1="T"_1 then empty:seq.word else 
   filter(1,"",instruction.a)

   
function find(coding:seq.inst,i:int,mangledname:word)  seq.word
   if i > length.coding then "not found" else
   let ins=coding_i
   if mangledname= (towords.ins)_1 then 
     let c=if   // "SIMPLE"_1 in flags.ins // length.cleancode.ins < 15   then 
      // assert length.code.ins < 15 report "LEN"+toword.length.code.ins // cleancode.ins  else empty:seq.sig
     astext5(coding,c) 
    else 
      find(coding,i+1,mangledname) 
      
function stripparsedfunc(src:seq.word) seq.word
if length.src > 0 ∧ (src)_1 = "parsedfunc"_1 then
         subseq(src ,toint.(src)_2 + 3, length.src) else src
      
function find2(coding:seq.inst, known:symbolset, sym2:symbol) libsym
  let mangledname=mangledname.sym2
  let t=find2(coding,known,mangledname)
  if isempty.t then libsym(resulttype.sym2,mangledname,"")
  else t_1
  
 use seq.sig
  
function find2(coding:seq.inst, known:symbolset, mangledname:word) seq.libsym
  let sym=lookupsymbol(known,mangledname) 
 // let ok=if isdefined.sym then true else let d=codedown.mangledname   length.d > 1 &and d_2 =   "builtin "
  assert  ok report "HJK"+mangledname //
  if last.towords.modname.sym in "builtin local para" then empty:seq.libsym else
  let t= find (coding,1,mangledname)
  let src=stripparsedfunc.if t="not found" then src.sym else t
     let src2= if src="PARAM 1"+mangledname+"builtinZinternal1Zinternal1" then
       "" else src
     [libsym(resulttype.sym,mangledname,src2)]
    
function close(intercode:intercode,   known:symbolset,toprocess:seq.libsym,have:set.word,processed:seq.libsym) seq.libsym 
     let more=asset.@(+,calls,"",toprocess)-have
     if isempty.more then processed+toprocess else 
    let new=@(+,find2(coding.intercode,known),empty:seq.libsym,toseq.more)
     close(intercode,known,new,have &cup more,processed+toprocess)
 
  
function find(t:worddict.libsym,s:symbol) seq.libsym lookup(t,mangledname.s)

function libmod (t:worddict.libsym, f:firstpass) seq.libmod
     if not.exportmodule.f &or isabstract.modname.f then empty:seq.libmod
     else  
       let e=sort.@(+,find.t,empty:seq.libsym,toseq.exports.f)
       assert length.e=cardinality.exports.f report "DIFF libmods"
      [libmod(false, abstracttype.modname.f,empty:seq.libsym,e, empty:seq.mytype)]
    
use seq.libmod

use seq.mytype

function add(t:worddict.libsym,l:libsym) worddict.libsym  add(t,fsig.l,l) 
  

function astext(s:seq.inst, ss:sig)seq.word
 let i=lowerbits.ss
 let f = towords.s_i
  if f_1 = "CONSTANT"_1 then   astext5(s,cleancode.s_i)+"RECORD"+toword.length.cleancode.s_i
  else if f_1 = "PARAM"_1 then"PARAM" + toword(- toint.f_2 - 1)
  else if f_1 in "SET WORD WORDS LOCAL LIT PARAM RECORD FREF EXITBLOCK BR BLOCK DEFINE"then f else [ f_1]

function astext5(s:seq.inst, d:seq.sig)seq.word @(+, astext.s,"", d)


----------------------------------

function addlibsym(s:libsym) int
      asinstconstant.[aseinst("WORD"+fsig.s) ,addwords.returntype.s ,addwords.instruction.s]
     

function addwords(t:seq.word) int aseinst("WORDS"+toword.length.t+t)

function addmytype(t:mytype) int  addwords(towords.t)

use seq.mytype

function addseq(s:seq.int) int let t=[ aseinst("LIT 0"), aseinst("LIT"+toword.length.s)]+s
 asinstconstant.t

 
function addlibmod(s:libmod) int 
    asinstconstant.[aseinst("LIT"+if parameterized.s then "1" else "0")
     ,aseinst("WORD"+modname.s)
     ,addseq.@(+,addlibsym,empty:seq.int,defines.s)
      ,addseq.@(+,addlibsym,empty:seq.int,exports.s)
    ,addseq.@(+,addmytype,empty:seq.int,uses.s)]

Function addlibmods(s:seq.libmod,i:intercode) intercode
    let b=length.additionalinst.0
    let last=addseq.@(+,addlibmod,empty:seq.int,s)
    let c=additionalinst(b+1)
    assert b=length.coding.i report "FAIL 15"
    assert last=b+length.c report "FAIL 16"
      intercode(  coding.i+c,defines.i)