Module typerep

use standard

use mytype

use set.typerep

use set.symdef

use symbol

use program

use seq.seq.mytype

use seq.mytype

use set.mytype

use seq.typerep

type typerep is tosymdef:seq.mytype

Function totypeseq(t:typerep) seq.mytype tosymdef.t


Export type:typerep 

function ?(a:typerep,b:typerep) ordering  first.tosymdef.a ? first.tosymdef.b

Function type(a:typerep) mytype  first.tosymdef.a

Function flatflds(a:typerep) seq.mytype  tosymdef.a << 1

Function typerep(t:mytype,flat:seq.mytype) typerep typerep([t]+flat)  

Function buildtypedict(zz1:set.symdef, types:seq.seq.mytype)    type2dict
 for  acc = empty:set.symbol, p = toseq.zz1 do
     acc + sym.p
/for(buildtypedict( acc ,types))

use set.symbol
 
Function buildtypedict(syms:set.symbol, types:seq.seq.mytype)    type2dict
 let typesused=for  acc = empty:seq.mytype, sym = toseq.syms do
     acc + typesused.sym 
/for(acc)
let typesyms=  for acc=empty:set.typerep,  tp=types do acc+ typerep( first.tp,   tp << 1  )  /for(acc)
for acc3 = toseq.typesyms, q = toseq.asset.typesused do
               let z=typerep( q , empty:seq.mytype)
                if z /in  typesyms then acc3 else acc3+z
             /for(resolvetypesize(acc3) )
             

function typesused(sym:symbol)seq.mytype
 { only includes parameter of seq and encoding and excludes types int, real, boolea, ptr, and T}
 for acc = empty:seq.mytype, t = types.sym do 
   let typ=if isseq.t ∨ isencoding.t then parameter.t else   t
   if typ ∈ [ typeint, typereal, typeboolean, typeptr, typeT] then acc else acc+ typ 
     /for(acc)
 
 function resolvetypesize(prg1:seq.typerep) type2dict
  let bx5 = checkflat(empty:set.typerep, prg1)
assert  isempty.unknown.bx5  report"flattype problem"
 + for acc10 ="", h = unknown.bx5 do
  acc10 + print.h 
  + if isflat.h then"T"else""/if
  + EOL
 /for(acc10)
 + " /p  /p known types /p"
 + for acc10 ="", h = toseq.known.bx5 do
  acc10 + print.h + EOL
 /for(acc10)
for acc=emptytypedict, d=toseq.known.bx5 do add( acc, type.d  ,flatflds.d) /for( acc)
 
function print(s:symdef) seq.word print.sym.s+print.code.s 

function print(h:typerep) seq.word for acc=print.type.h , z= flatflds.h do acc+print.z /for(acc)

 function checkflat(types:set.typerep, unknown:seq.typerep)checkflatresult2
 for known = types, notflat = empty:seq.typerep,   p = unknown do
   if isflat.p /or   abstracttype.type.p="$base"_1  /or type.p =type? then next(known + p, notflat )
   else let new=expandflat(p, types)
     if isflat.new then next(known+new,notflat) else  next(known, notflat + new )
 /for( if isempty.notflat /or length.unknown=length.notflat then 
 checkflatresult2(known, notflat )
 else checkflat(known, notflat)
)



type checkflatresult2 is known:set.typerep, unknown:seq.typerep 

function isflat(p:typerep)boolean
 if isempty.flatflds.p then false
 else
  for state = true, t = flatflds.p while state do
   t ∈ [ typeint, typeT, typeboolean, typereal,typeptr] ∨ isseq.t ∨ isencoding.t
  /for(state)

function expandflat(p:typerep,types:set.typerep)typerep
 let flatflds=flatflds.p
 if isempty.flatflds then
     let f3=findelement(typerep(abstracttypeof2.type.p,empty:seq.mytype),types)
      if isempty.f3 then p 
      else typerep(type.p,replaceT(parameter.type.p,flatflds.f3_1) )
 else 
  for acc = empty:seq.mytype, unchanged = true, t = flatflds.p do
  if t ∈ [ typeint, typeT, typeboolean, typereal] ∨ isseq.t ∨ isencoding.t then
    next(acc + t, unchanged)
   else
      let   f=findelement(typerep(t,empty:seq.mytype),types)
      if isempty.f then
         let f3=findelement(typerep(abstracttypeof.t,empty:seq.mytype),types)
         if isempty.f3 then next(acc + t, unchanged)
         else next(acc + replaceT(parameter.t,flatflds.f3_1 ), false)
     else next(acc + flatflds.f_1, false)
      /for(if unchanged then p else typerep(type.p,    acc )/if)

function replaceT(with:mytype,typs:seq.mytype) seq.mytype
 for acc=empty:seq.mytype,t=typs do acc+replaceT(with,t) /for(acc)
 
use seq.symbol
 
Function basetype(type:mytype, addsize: type2dict)mytype
   if isseq.type then
     let para=parameter.type
     if para =typebyte /or para =typebit then type else 
     seqof.coretype(parameter.type,addsize,6)
   else coretype(type,addsize)    

Function blocksym(basetype:mytype)symbol
let p = parameter.basetype
let p2 = seqof.if p = typebyte ∨ p = typebit ∨ p = typeboolean then typeint else p
 symbol(moduleref."tausupport","blockIt", p2, p2)

   
Function deepcopybody(type:mytype, typedict:type2dict)seq.symbol
  if type = typeint ∨ type = typeword ∨ isencoding.type then [ Local.1]
 else if isseq.type then
 let basetype =  basetype(  type,typedict)
 if basetype = typeint ∨ basetype = typereal ∨ basetype = typeboolean then [ Local.1, blocksym.basetype]
  else
   let cat = symbol(tomodref.type,"+", [ type, parameter.type], type)
   let resulttype = basetype
   let elementtype = parameter.basetype
   let element = symbol(moduleref("$for", elementtype),"element", empty:seq.mytype, elementtype)
   let acc = symbol(moduleref("$for", typeptr),"acc", empty:seq.mytype, typeptr)
   [Sequence(elementtype,0)]
    + [ Local.1, acc, element, acc, element, deepcopySym( parameter.type), cat, Littrue, acc, symbol(moduleref("builtin", typeint),"forexp", [ resulttype, resulttype, resulttype, elementtype, typeptr, typeboolean, resulttype], resulttype)
    ]
    + blocksym.basetype
 else
  let subflds =  flatflds(typedict,type)
  if length.subflds = 1 then
    { only one element in record so type is not represent by actual record }[ Local.1]
    + deepcopySym(first.subflds)
   else 
    for     fldno=1, fldkinds=empty:seq.mytype, result= empty:seq.symbol,fldtype=subflds do
  let kind = basetype(  fldtype,typedict)
   next(fldno+1,fldkinds + kind, result + [ Local.1,Lit(fldno - 1), Getfld.kind,   deepcopySym( fldtype)])
/for(result + [ Record.fldkinds])