module postbind

use standard

use symbol

use pro2gram
 
use seq.symbol

use set.symbol

use seq.seq.symbol

use set.symdef

use seq.symdef

use seq.mytype

use seq.seq.mytype

  use encoding.symbol

   use seq.encodingpair.symbol

use intdict.seq.symbol

use program

use otherseq.mytype

use otherseq.word


function handletemplate(dict:set.symbol, sym:symbol, org:seq.word, sourceX:program, tempX:program)seq.symbol
let fx = lookupcode(tempX, sym)
if isdefined.fx then
  if isdefined.lookupcode(sourceX, sym)then [ sym]else [ sym] + code.fx
 else
  let k = lookupsymbol(dict, sym)
  assert cardinality.k = 1 report"Cannot find template for" + print.sym + "while processing" + org
    assert sym ≠ k_1 report"ERR12" + print.sym + print.k_1
    let dd = lookupcode(sourceX, k_1)
    if isdefined.dd then [ k_1]
     else { handles parameterized unbound cases like ?(int arc, int arc)graph.int }handletemplate(dict, k_1, org, sourceX, tempX)

/function buildcode(acc:int, w:word)int
 acc * 2 + if w = first."real"then 1 else 0
 
 
{ base types are int real boolean ptr seq.int seq.real seq.boolean seq.ptr seq.byte seq.bit 
   seq.packed2 seq.packed3 seq.packed4 seq.packed5 seq.packed6 or $base.x where x is a integer}
            
Function  prescan2(   prg:pro2gram) pro2gram 
      for  acc=empty:set.symdef ,  p=tosymdefs.prg do
         for  result = empty:seq.symbol, sym = code.p do
          {if not.isempty.result ∧ last.result = PreFref then
               result >> 1+Fref.sym
           else} if  islocal.sym then
                 result +  Local.value.sym
           else if isdefine.sym then  result+Define.value.sym
           else result + sym
      /for(acc+symdef( sym.p,result))
      /for(pro2gram.acc)      
 
Function postbind(alltypes:type2dict, dict:set.symbol, roots:seq.symbol, theprg:program, templates:program)pro2gram
let root = symbol(moduleref."W","Wroot", typeint)
   let discard=for acc=0 ,r=roots do let discard2=encode.r 0 /for(0)
 pro2gram.asset.usedsyms(theprg,alltypes,0,empty:seq.symdef,templates,dict)
  
  function usedsyms(source:program ,typedict:type2dict,last:int,result:seq.symdef, tempX:program
  , dict:set.symbol) seq.symdef
     let a=  encoding:seq.encodingpair.symbol 
     if length.a=last   then result
    else 
    for  acc=result,   p=subseq(a,last+1,length.a) do
     let sym1=data.p
    if isspecial.sym1 /or isconst.sym1 
             /or name.module.sym1 /in "builtin internal $for $global" 
             /or name.sym1 /in "abort" then acc
             else
          let lr1 = lookupcode(source, data.p)
          let org=print.data.p
            let r=if isdefined.lr1 then 
            postbind3b(typedict,dict,symdef(data.p,code.lr1),source) 
            else  if istype.data.p then
             let p2 =  deepcopybody(resulttype.data.p,typedict )
             postbind3b(typedict,dict,symdef(data.p,p2),source)
            else 
               let fx = handletemplate(dict, data.p, org, source, tempX)
               let k = first.fx
               if length.fx=1 then
                let code= for paras=empty:seq.symbol,i=arithseq(nopara.k,1,1) do paras+Local.i /for(paras+k)
                postbind3b(typedict,dict,symdef(data.p,code),source)
               else 
                assert length.fx > 1 report "KLJ??"+print.k+print.data.p
                   postbind3b(typedict,dict,symdef(k,fx << 1),source) 
              let discard=for acc2=symbolref.EqOp, sym=code.r   do  symbolref.sym /for(acc2)
            acc+symdef(data.p,code.r) 
         /for(
           usedsyms(source, typedict,length.a,acc,tempX,dict)
           )


function postbind3b(typedict:type2dict, dict:set.symbol, sd:symdef, source:program)symdef
let modpara = para.module.sym.sd
 let pdict = for pmap = empty:intdict.seq.symbol, parano = 1, e = constantseq(10000, 1)while parano ≤ nopara.sym.sd do 
               next(add(pmap, parano, [ Local.parano]), parano + 1)
            /for(pmap)
for nextvar = nopara.sym.sd + 1, map = pdict,result = empty:seq.symbol ,  sym = code.sd do
      if name.module.sym ∈ "$define"then
      next(nextvar + 1, replace(map, value.sym, [ Local.nextvar]),   result + Define.nextvar)
     else if name.module.sym ∈ "$local"then
       let t = lookup(map, value.sym)
        next(nextvar, map,   result + t_1)  
     else  if isspecial.sym then
     let p2 = if isSequence.sym then Sequence(parameter.basetype(  replaceT(modpara, resulttype.sym),typedict), nopara.sym)
            else if isstart.sym then Start.basetype( replaceT(modpara, resulttype.sym),typedict)
          else sym
       next(nextvar,map,result + p2 )
    else if isconst.sym ∨ inmodule(sym,"$global") ∨ inmodule(sym,"internal") /or sym=PreFref /or sym= Optionsym then 
       next(nextvar,map,result + sym)
    else if inmodule(sym,"$for")then next(nextvar,map,result + replaceTsymbol(modpara, sym) )
    else
     let lr1 = lookupcode(source, sym)
     let newsym = if issimple.module.sym.sd ∨ isdefined.lr1 then sym else replaceTsymbol(modpara, sym)
     if isdefined.lr1 then
      let p2 =if"VERYSIMPLE"_1 ∈ getoption.code.lr1 /and (isempty.result /or last.result /ne PreFref )then
               subseq(code.lr1, nopara.newsym + 1, length.code.lr1 - 2)
              else 
                assert target.lr1=sym report "PPP"+print.target.lr1+print.sym
                 [ target.lr1]
      next(nextvar,map,result + p2 )
    else if inmodule(sym,"builtin")then
         if  name.sym ∈ "primitiveadd" then
        let encodingtype = typeref."encoding encoding. "
       let encodingstatetype = typeref."encodingstate encoding. "
       let encodingpairtype = typeref."encodingpair encoding. "
       let addefunc = symbol(moduleref("encoding", para.module.newsym),"add", [ addabstract(encodingstatetype, para.module.newsym), addabstract(encodingpairtype, para.module.newsym)], addabstract(encodingstatetype, para.module.newsym))
       let add2 = symbol(internalmod,"addencoding", [ typeint, typeptr, typeint, typeint], typeint)
       let dc = deepcopysym(typedict, addabstract(encodingpairtype, para.module.newsym))
         next(nextvar+1,map,result+[ PreFref,addefunc, PreFref,dc, add2] )
      else if name.sym ∈ "getinstance"then
          let get = symbol(internalmod,"getinstance", typeint, typeptr)
            next(nextvar+2,map,result + encodenocode(para.module.newsym,nextvar) +   get  )
        else  next(nextvar,map   
      ,    if name.sym ∈ "pushflds" then
            if iscoretype.para.module.newsym then result
            else 
             let t = flatflds(typedict,para.module.newsym)
             if isempty.t /or typeT ∈ t  then 
                    result+sym
             else if length.t=1  then result
             else 
              for newresult=result >> 1 , idx=0, x=t do
                 next(newresult+ [last.result,Lit.idx,Getfld.x],idx+1)
              /for(newresult) 
      else  if name.sym ∈ "buildrecord" then
        let t = flatflds(typedict,para.module.newsym)
        result+if isempty.t /or typeT ∈ t then sym  else  Record.t
    else  if name.sym ∈  "bitcast"  then
     let a = coretype(first.paratypes.sym, typedict)
      let b = coretype(resulttype.sym, typedict)
      if a = b then result else   result + symbol(internalmod,"bitcast", a, b)
    else result+  if name.sym ∈ "processresult"then
            [ Lit.2 , Getfld.coretype( para.module.newsym,typedict )]
   else [ if name.sym ∈ "typesize"then
       let typ=para.module.newsym
          if typ = typeint ∨ typ = typereal ∨ typ = typeptr /or isseq.typ then Lit.1
              else       let t = flatflds(typedict,typ)  
        if isempty.t /or typeT ∈ t then sym else Lit.length.t
  else     if name.sym ∈ "length"then  GetSeqLength
else if name.sym ∈ "packed"then 
 let typ=seqof.coretype(para.module.newsym, typedict)
          symbol(moduleref( "tausupport"),"blockIt", typ,typ)
     else if name.sym ∈ "aborted"then   symbol(internalmod,"aborted", typeptr, typeboolean)
 else if name.sym ∈ "assert"then
      abortsymbol.coretype(para.module.newsym, typedict)
        else if name.sym ∈ "_"then
     let seqtype = basetype(first.paratypes.newsym,typedict)
          symbol(internalmod,"indexseq45", seqtype, typeint,  parameter.seqtype )
       else if name.sym ∈ "getseqtype"then   GetSeqType
      else if name.sym ∈ "set"then
         setSym.coretype(para.module.sym, typedict)
      else if name.sym = "forexp"_1 then  
  let paras = for acc = empty:seq.mytype, p = paratypes.newsym do
  acc + if"$base"_1 ∈ print.p then p else  basetype( p,typedict)
 /for(acc)
  symbol(moduleref."builtin","forexp", paras, last.paras)
      else  if name.sym = "createthreadY"_1 then
        let paras = for paras = empty:seq.mytype, p = paratypes.sym do paras + coretype(replaceT(modpara, p), typedict)/for(paras)
       let rt = processof.coretype(replaceT(modpara, parameter.resulttype.sym), typedict)
        symbol(builtinmod.rt,"createthreadY", paras, typeptr)
       else if name.sym ∈ "fld getfld"then
            let typ=resulttype.newsym  
            if iscoretype.typ then  Getfld.typ  
            else if isabstract.typ then sym 
            else
            let a=flatflds( typedict,typ)
            assert not.isempty.a report "cannot find type getfld" +print.typ
            if length.a > 1 then 
              symbol(internalmod,"GEP", seqof.typeptr, typeint, typeptr)
            else   Getfld.first.a  
        else if name.sym ∈ "empty" then Sequence(coretype(para.module.newsym, typedict),0)
  else
        assert name.sym /in "offsets build" report "post bind"+print.sym
     sym
     ])
      else    next(nextvar,map,result+newsym )  
       /for(symdef(sym.sd, result))
       
 function iscoretype(typ:mytype) boolean
 typ =  typeint /or typ=typereal   /or typ=typeptr /or typ=typeboolean /or isseq.typ /or isencoding.typ

  function encodenocode(typ:mytype,varno:int)seq.symbol
  let gl = symbol4(moduleref."$global","global"_1, typ, empty:seq.mytype, seqof.typeint)
  let encodenosym = symbol(moduleref."tausupport","encodingno", seqof.typeword, typeint)
  if typ = typeref."typename tausupport. "then [  Lit.2 ]
  else if typ = seqof.typeref."char standard ."then  [   Lit.1 ]  
 else
  ifthenelse([ gl,Lit.0,Getfld.typeint,Define.varno,
     Local.varno , Lit.0, EqOp], [   gl, Words.print.typ, encodenosym, setSym.typeint, Define(varno+1), gl  
      ,Lit.0,Getfld.typeint],[ Local.varno],typeint)

function basetype(type:mytype, addsize: type2dict)mytype
   if isseq.type then
     let para=parameter.type
     if para =typebyte /or para =typebit then type else 
     seqof.coretype(parameter.type,addsize,6)
   else coretype(type,addsize)    

function blocksym(basetype:mytype)symbol
let p = parameter.basetype
let p2 = seqof.if p = typebyte ∨ p = typebit ∨ p = typeboolean then typeint else p
 symbol(moduleref."tausupport","blockIt", p2, p2)
       
function deepcopysym(typedict:type2dict, type:mytype) symbol
 if type =typereal /or type=typeint then deepcopySym(type) else
 let z=flatwithtype(typedict,type)
 assert not.isempty.z report  "deepcopy cannot find type"+print.type
   deepcopySym(first.z)
        
function deepcopybody(type:mytype, typedict:type2dict)seq.symbol
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
    + [ Local.1, acc, element, acc, element, deepcopysym(typedict, parameter.type), cat, Littrue, acc, symbol(moduleref("builtin", typeint),"forexp", [ resulttype, resulttype, resulttype, elementtype, typeptr, typeboolean, resulttype], resulttype)
    ]
    + blocksym.basetype
 else
  let subflds =  flatflds(typedict,type)
  if length.subflds = 1 then
    { only one element in record so type is not represent by actual record }[ Local.1]
    + deepcopysym(typedict, first.subflds)
   else 
    for     fldno=1, fldkinds=empty:seq.mytype, result= empty:seq.symbol,fldtype=subflds do
  let kind = basetype(  fldtype,typedict)
   next(fldno+1,fldkinds + kind, result + [ Local.1,Lit(fldno - 1), Getfld.kind,   deepcopysym(typedict, fldtype)])
/for(result + [ Record.fldkinds])
