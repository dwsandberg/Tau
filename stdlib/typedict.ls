Module typedict

use standard

use mytype

use set.typeentry

use set.symdef

use symbol

use program

use seq.seq.mytype

use seq.mytype

use set.mytype

use seq.typeentry

Export type:typeentry

type typeentry is totypeseq:seq.mytype

function ?(a:typeentry,b:typeentry) ordering  first.totypeseq.a ? first.totypeseq.b

function type(a:typeentry) mytype  first.totypeseq.a

function flatflds(a:typeentry) seq.mytype  totypeseq.a << 1

function typeentry(t:mytype,flat:seq.mytype) typeentry typeentry([t]+flat)  

Function buildtypedict(zz1:set.symdef, types:seq.seq.mytype)    typedict
 for  acc = empty:set.symbol, p = toseq.zz1 do
     acc + sym.p
/for(buildtypedict( acc ,types))

Function    addtypes(alltypes:typedict,syms:set.symbol)   typedict
 let typesused=for  acc = empty:seq.mytype, sym = toseq.syms do
  if isstart.sym /or isSequence.sym then acc+typesused.sym 
  else if isconst.sym ∨ isGlobal.sym ∨ isInternal.sym   /or sym= Optionsym   
     /or  inModFor.sym 
     /or    isspecial.sym   then  acc
   else
     if issimple.module.sym then acc else  acc+para.module.sym  /if +
      typesused.sym 
/for(acc)
 for acc=alltypes ,d= toseq.asset.typesused do 
 if d= type? /or abstracttypename.d /in"$base"  then acc else
 addtype(acc,d)  /for(acc)
 
 function print(t:seq.mytype) seq.word for txt="",a=t do  txt+print.a /for (txt)

Function    addtype(alltypes:typedict,type:mytype)   typedict
   if type   ∈ [ typeint, typeT, typeboolean, typereal,typeptr] then alltypes
  else 
   if isseq.type then addtype(alltypes,parameter.type)
  else 
   let t=  findelement(typeentry(type,empty:seq.mytype),totypedict.alltypes)
  if not.isempty.t then alltypes 
  else 
    {assert  abstracttypename.type /nin "lexaction1 nodemap" report "lexxx"+if isempty.t then "T" else "F" /if+print.alltypes}
   let flatflds=expandflat(type,empty:seq.mytype,totypedict.alltypes) 
   let newtr=typeentry(type,flatflds)
    if isflat.newtr then 
     { add to typedict and then check to make sure parameters are in typedict }
     for acc= typedict(totypedict.alltypes+newtr) ,subfld = flatflds    do
        if   isseq.subfld  /or isencoding.subfld   
        then addtype(acc,subfld) 
        else acc
     /for(acc)
     else  
     { add types not in  typedict  and try again }
      for acc=alltypes, subfld = flatflds    do
        if subfld ∈ [ typeint, typeT, typeboolean, typereal,typeptr]  /or isseq.subfld /or isencoding.subfld  
        then acc
      else 
          addtype(acc,subfld)
     /for( assert cardinality.totypedict.alltypes < cardinality.totypedict.acc report "PROBLEM"+print.type
     +"flat:"+for txt="",g=flatflds do txt+print.g /for(txt+EOL)+print.acc
       addtype(acc,type))
  
use set.symbol

Function check(smalldict:typedict,bigdict:typedict) typedict
   for small=smalldict,      atyprep=  toseq.totypedict.bigdict do 
      let t=type.atyprep
        let new=addtype(smalldict,t)
     assert  isseq.t /or flatwithtype(new,t)=flatwithtype(bigdict,t) report "check"+print.t
      +"flat:"+for txt="",g=flatwithtype(bigdict,t) do txt+print.g /for(txt+EOL)
      +"flat:"+for txt="",g=flatwithtype(new,t) do txt+print.g /for(txt+EOL)
     new
    /for(small)
 
Function buildtypedict(syms:set.symbol, types:seq.seq.mytype)    typedict
 let typesused=for  acc = empty:seq.mytype, sym = toseq.syms do
     acc + typesused.sym 
/for(acc)
let typesyms=  for acc=empty:set.typeentry,  tp=types do acc+ typeentry( first.tp,   tp << 1  )  /for(acc)
for acc3 = toseq.typesyms, q = toseq.asset.typesused do
               let z=typeentry( q , empty:seq.mytype)
                if z /in  typesyms then acc3 else acc3+z
             /for(resolvetypesize(acc3) )
             

             

function typesused(sym:symbol)seq.mytype
 { only includes parameter of seq and encoding and excludes types int, real, boolea, ptr, and T}
 for acc = empty:seq.mytype, t = types.sym do 
   let typ=if isseq.t ∨ isencoding.t then parameter.t else   t
   if typ ∈ [ typeint, typereal, typeboolean, typeptr, typeT] then acc else acc+ typ 
     /for(acc)
 
 function resolvetypesize(prg1:seq.typeentry) typedict
  let bx5 = checkflat(empty:set.typeentry, prg1)
assert  isempty.unknown.bx5  report"recursive type problem: /br"
 + for acc10 ="", h = unknown.bx5 do
  acc10 + print2.h   + EOL
 /for(acc10)
 {+ " /p  /p known types /p"
 + for acc10 ="", h = toseq.known.bx5 do
  acc10 + print.h + EOL
 /for(acc10)}
for acc=emptytypedict, d=toseq.known.bx5 do add( acc, type.d  ,flatflds.d) /for( acc)
 
function print(s:symdef) seq.word print.sym.s+print.code.s 

function print(h:typeentry) seq.word for acc=print.type.h , z= flatflds.h do acc+print.z /for(acc)

function print2(h:typeentry) seq.word for acc="type"+print.type.h+"is" , z= flatflds.h do acc+print.z+"," /for(acc >> 1)


 function checkflat(types:set.typeentry, unknown:seq.typeentry)checkflatresult2
 for known = types, notflat = empty:seq.typeentry,   p = unknown do
   if isflat.p /or   abstracttypename.type.p="$base"_1  /or type.p =type? then next(known + p, notflat )
   else let new=expandflat(p, types)
     if isflat.new then next(known+new,notflat) else  next(known, notflat + new )
 /for( if isempty.notflat /or length.unknown=length.notflat then 
 checkflatresult2(known, notflat )
 else checkflat(known, notflat)
)



type checkflatresult2 is known:set.typeentry, unknown:seq.typeentry 

function isflat(p:typeentry)boolean
 if isseq.type.p then true
 else if isempty.flatflds.p then false
 else
  for state = true, t = flatflds.p while state do
   t ∈ [ typeint, typeT, typeboolean, typereal,typeptr,typeword] ∨ isseq.t ∨ isencoding.t
  /for(state)

function expandflat(p:typeentry,types:set.typeentry)typeentry
  let newflat=expandflat(type.p ,flatflds.p,types )  
  if newflat=flatflds.p then p else typeentry(type.p,    newflat )
 
 function expandflat(type:mytype,flatflds:seq.mytype,types:set.typeentry) seq.mytype
 if isempty.flatflds then 
     let f3=findelement(typeentry(abstracttype.type ,empty:seq.mytype),types)
      if isempty.f3 then flatflds
      else  
        expandflat(type,replaceT(parameter.type ,flatflds.f3_1),types)  
 else 
 for acc = empty:seq.mytype, unchanged = true, t = flatflds  do
  if t ∈ [ typeint, typeT, typeboolean, typereal,typeword] ∨ isseq.t ∨ isencoding.t then
    next(acc + t, unchanged)
   else
      let   f=findelement(typeentry(t,empty:seq.mytype),types)
      if isempty.f   then
         let t2=  (abstracttype.t) 
         if t2=t then next(acc + t, unchanged)
         else 
         let f3=findelement(typeentry(t2,empty:seq.mytype),types)
         {assert {print.t /ne "set.arc.T"} isempty.f3   report "K"+print.t+"K"+print.t2 }
         if isempty.f3 then next(acc + t, unchanged)
         else next(acc + replaceT(parameter.t,flatflds.f3_1 ), false)
     else next(acc + flatflds.f_1, false)
      /for(if unchanged then flatflds else    expandflat(type,acc,types) /if)

function replaceT(with:mytype,typs:seq.mytype) seq.mytype
 for acc=empty:seq.mytype,t=typs do acc+replaceT(with,t) /for(acc)
 
use seq.symbol
 
Function basetype(type:mytype, addsize: typedict)mytype
   if isseq.type then
     let para=parameter.type
     if para =typebyte /or para =typebit then type else 
     seqof.coretype(parameter.type,addsize,6)
   else coretype(type,addsize)    
   
type typedict is totypedict:set.typeentry

Function print(dict:typedict) seq.word
   for txt="", tr=toseq.totypedict.dict do   for acc2=txt,  t=totypeseq.tr do acc2+print.t /for(acc2+EOL) /for(txt)

Export type:typedict


Function emptytypedict typedict typedict.empty:set.typeentry

Function add(alltypes:typedict,t:mytype,flatflds:seq.mytype) typedict
   typedict(totypedict.alltypes +typeentry(t,flatflds))
      
Function    flatflds(alltypes:typedict,type:mytype) seq.mytype
 {assert not.isseq.type /or parameter.type=typeT report "flattype"+print.type+stacktrace}
  let t=  findelement(typeentry(type,empty:seq.mytype),totypedict.alltypes)
  if isempty.t then empty:seq.mytype
  else flatflds.t_1  
  
Function    flatwithtype(alltypes:typedict,type:mytype) seq.mytype
   let t=  findelement(typeentry(type,empty:seq.mytype),totypedict.alltypes)
 if isempty.t then empty:seq.mytype
  else [type.t_1] +flatflds.t_1  
        
  
Function coretype(typ:mytype, alltypes:typedict) mytype  coretype(typ,alltypes,{6} 0)
    
Function coretype(typ:mytype, alltypes:typedict,maxsize:int)mytype
 if typ = typeint ∨ typ = typeboolean ∨ typ = typeptr ∨ typ = typereal
 ∨ typ = typeT then
  typ
 else if isseq.typ then typeptr
 else if isencoding.typ then typeint
 else
   let flatflds=flatflds(alltypes,typ)
  if isempty.flatflds then typ else 
   let fldsize=length.flatflds 
  if fldsize = 1 then coretype(first.flatflds, alltypes)else
      if fldsize > min(maxsize ,length.packedtypes+1)     then typeptr
      else packedtypes_(fldsize-1)
     
 


   
