Module convertlibtyp

use stdlib

use libscope

use newsymbol

use seq.libtype

use seq.mytype

use seq.liblib

use seq.symbol

use seq.libmod

use seq.libsym

run convertlibtype test2

use set.libtype

use processtypes

use seq.mod2desc

use passcommon

use set.symbol

use set.syminfo

use other

/type firstpass is record modname:mytype, uses:seq.mytype, defines:set.symbol, exports:set.symbol, unboundexports:seq.symbol, 
unbound:set.symbol, exportmodule:boolean

Function exportmodule(firstpass) boolean export

Function defines(firstpass) set.symbol export

Function exports(firstpass) set.symbol export

Function modname(firstpass) mytype export

Function tofirstpass(m:mod2desc) firstpass 
  firstpass( modname.m, empty:seq.mytype, @(+, tosymbol, empty:set.symbol, toseq.defines.m), 
 @(+, tosymbol, empty:set.symbol, toseq.export.m), empty:seq.symbol, empty:set.symbol, not.isprivate.m) 

function tosymbol(ls: syminfo)symbol 
  symbol(mangled.ls,   returntype.ls, @(+, replaceT.parameter.modname.ls, empty:seq.mytype, paratypes.ls), 
  name.ls, modname.ls, instruction.ls)

Function getalllibtypes seq.libtype
  let m=  @(+,mods,empty:seq.libmod,  libs )
    toseq.asset.getlibtypes.@(+,defines,empty:seq.libsym,m)


Function  todesc(alltypes:set.libtype,l:libtype) symbol
 let t=mytype((if abstract.l then  "T" else "")+name.l)
 let flat=@(+,deepcopytypes3.alltypes,empty:seq.mytype,subtypes.l)
 // assert subtypes.l=flat report "ERR555"+@(+,print,"",subtypes.l)+"\\\"+@(+,print,"",flat) //
 let code=[kind.l,toword.LIT.size.l]+@(+,print,"",flat) 
 symbol(merge("typedesc:"+ print.t), mytype."internal", empty:seq.mytype, mytype."word seq", "WORDS"+toword.length.code+code)
  
function fromdesc(s:symbol) libtype
  let a =towords.decode(name.s) 
    libtype(a_3,"T"_1 in a, (src.s)_3,rebuildsubtypes(src.s+"X",6,5),offset.0,"")
    
Function getlibtypes(s:seq.libsym) seq.libtype
let t2=@(+,aslibtype,empty:seq.libtype,s)
let sizes=processsize(t2,empty:set.sizecal,empty:seq.libtype,1)
 @(+,assignsize(sizes),empty:seq.libtype,t2)

    
function aslibtype(s:libsym) seq.libtype
  if  not("WORDS"_1 in instruction.s) then empty:seq.libtype else 
  let a =towords.decode((codedown.fsig.s)_1_1) 
  if  subseq(a,1,2)="typedesc:" then 
    [libtype(a_3,"T"_1 in a, (instruction.s)_3,rebuildsubtypes(instruction.s+"X",6,5),offset.0,"")]
  else empty:seq.libtype

function rebuildsubtypes(desc:seq.word, i:int, starttype:int)seq.mytype
 if i > length.desc 
  then  empty:seq.mytype
  else if desc_i ="."_1 
  then rebuildsubtypes(desc, i + 2,   starttype)
  else   
   [mytype.unparse(subseq(desc, starttype, i - 1),1)]+rebuildsubtypes(desc, i+1 , i)
  
  function unparse(t:seq.word,i:int) seq.word
    if length.t=i then [t_i]
    else 
        unparse(t,i+2)+t_i
  
function print3(l:libtype) seq.word
  "&br"+(if abstract.l &and "T"_1 &ne name.l then  "T"+name.l else [name.l])+kind.l+@(+,print,"",subtypes.l)+print.size.l
  
function check(a:seq.libtype,b:seq.libtype,i:int) seq.word
if print3.a_i=print3.b_i then "OK" else "&br"+print3.a_i +"&br"+print3.b_i



/Function test2 seq.word
// let code="struct 3 word seq.word seq.word"
@(+,print,"",rebuildsubtypes(code+"X",4,3))
//
let typs=typesx.libs_1
let t3=getlibtypes(defines.last.mods.libs_1)
@(+,check(typs,t3),"",arithseq(length.typs,1,1))
 
let sizes=processsize(typs,empty:set.sizecal,empty:seq.libtype,1)
 @(+,print.sizes,"",typs)
 

type sizecal is record name:mytype, size:offset

function print(s:sizecal) seq.word "&br"+print.name.s+print.size.s

function ?(a:sizecal,b:sizecal)  ordering  name.a ? name.b

use seq.sizecal

use set.sizecal

function processsize(l:seq.libtype, sizes:set.sizecal,toprocess:seq.libtype,i:int)  set.sizecal
if i > length.l then 
  if  length.l=length.toprocess &or length.toprocess=0 then sizes 
  else processsize(toprocess,sizes,empty:seq.libtype,1)
  else 
 let x=typesize(sizes,l_i)
 if LIT.x &ge 0 then processsize(l,sizes+sizecal(mytype.[name.l_i],x),toprocess,i+1) 
 else processsize(l,sizes,toprocess+l_i,i+1)

function typesize(sizes:set.sizecal,t:mytype) offset
  if abstracttype.t in "encoding seq int" then offset(1) else
  if mytype."T"=t then Tsize else
   let f=  findelement(  sizecal(t,offset(0)),sizes)
   if isempty.f then 
    if not.iscomplex.t then offset(-100)
    else 
      let g=findelement(  sizecal(mytype.[abstracttype.t],offset(0)),sizes)
     if isempty.g then  offset(-100)
     else 
      let sz=   typesize(sizes,parameter.t) 
      if LIT.sz &ge 0 then 
       compose(size.g_1,sz)
      else
    offset(-100) else size.f_1
  
function typesize(sizes:set.sizecal,t:libtype)  offset
 if kind.t in "sequence type" then offset(1)
 else  @(+,typesize.sizes,offset(0),subtypes.t)
 

function assignsize(sizes:set.sizecal,t:libtype) libtype
   let b = findelement( sizecal(mytype.[name.t],offset.0),sizes)
  assert not.isempty.b report    ">>> nosize" +name.t
libtype(name.t, abstract.t, kind.t, subtypes.t, size.b_1, "")


function isab(t:mytype) boolean    { (towords.t)_1="T"_1  }

function print(sizes:set.sizecal,t:libtype) seq.word
  let a= "&br"+name.t+(if abstract.t then ".T" else "")+kind.t+print.size.t+@(+,print,"",subtypes.t)+fldnames.t
  assert @(&or,isab,false,subtypes.t)=abstract.t &or name.t in "encoding erecord"  report "??3?"+a
  let b = findelement( sizecal(mytype.[name.t],offset.0),sizes)
  if isempty.b then  a+">>> nosize" else 
   assert size.b_1=size.t report a+">>>"+print.size.b_1+print.size.t
   a
   
