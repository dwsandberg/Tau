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

use otherseq.mytype

use otherseq.word

type findabstractresult  is sd:symdef,modpara:mytype

use seq.findabstractresult 

function xxx(templates:pro2gram,sym:symbol)   seq.findabstractresult
     for  acc=empty:seq.findabstractresult , sd=toseq.data.templates do
     if name.sym=name.sym.sd  /and  para.module.sym.sd=typeT /and nopara.sym=nopara.sym.sd  
     /and name.module.sym.sd=name.module.sym     
      then 
      let z= for Tis=type? ,  idx=1,   t= types.sym.sd do
             let S=solveT(t,(types.sym)_idx) 
             if S=type? then 
              {assert t=(types.s)_idx report "XXXXX"+print.t+print.(types.s)_idx}
             next(Tis,idx+1) else next(S,idx+1)
            /for(Tis)
       if ?2(sym,replaceTsymbol(z,sym.sd)) =EQ  then 
        if sym ? sym.sd =EQ  /or isunbound.sym.sd then acc else
           acc+findabstractresult (sd,z)  
          else acc
    else  acc
    /for(
     acc)

/Function findabstract(all:set.passsymbols, s:symbol)seq.findabstractresult
let a = findelement(passsymbols(module.s, empty:set.symbol, empty:set.symbol, empty:set.symbol, empty:set.modref, empty:set.mytype, empty:seq.symtextpair)
, all
)
if isempty.a then empty:seq.findabstractresult
 else
  for acc = empty:seq.findabstractresult, e = toseq.defines.a_1 do
   if name.e = name.s ∧ nopara.e = nopara.s  then
      let z= for Tis=type? ,  idx=1,   t= types.e do
             let S=solveT(t,(types.s)_idx) 
             if S=type? then 
              {assert t=(types.s)_idx report "XXXXX"+print.t+print.(types.s)_idx}
             next(Tis,idx+1) else next(S,idx+1)
            /for(Tis)
    if  ?2(s,replaceTsymbol(z, e)) =EQ  then
       if s ? e =EQ /or isunbound.e then acc else
       acc + findabstractresult(e,z)
    else acc
   else acc
  /for(acc) 

function handletemplate(dict:set.symbol, sym:symbol, org:seq.word,   templates:pro2gram,compiled:set.symbol)seq.symbol
if isunbound.sym then
    let k = lookupsymbol(dict, sym)
    assert cardinality.k = 1 report"Cannot find template for" + print.sym + "while processing" + org+stacktrace
    assert sym ≠ k_1 report"ERR12" + print.sym + print.k_1
     if   issimple.module.k_1 /or k_1 /in compiled then [ k_1]
     else  
      assert not.isunbound.k_1 report "shound not be unbound"+print.k_1
      handletemplate(dict, k_1, org,   templates,compiled)
else
   let gx=xxx(templates,sym)
    assert length.gx = 1 report"Cannot find template for" + print.sym + "while processing" + org+stacktrace
      let fx2= for newcode=empty:seq.symbol,sym2 = code.sd.gx_1 do   newcode+ replaceTsymbol(modpara.gx_1, sym2)
                 /for(newcode) 
    {if not.isempty.getCode(sourceX, sym) then [ sym] else} [ sym] +  fx2


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
 
Function postbind(alltypes:type2dict, dict:set.symbol, roots:seq.symbol, theprg:pro2gram, templates:pro2gram,compiled:set.symbol)pro2gram
let root = symbol(moduleref."W","Wroot", typeint)
   let discard=for acc=0 ,r=roots do let discard2=encode.r 0 /for(0)
{let prg2=handletemplatesX( tosymdefs.theprg,asset.tosymdefs.theprg,templates,alltypes,compiled,dict)    
} pro2gram.asset.usedsyms(theprg,alltypes,0,empty:seq.symdef,templates,dict,compiled)
  
  function usedsyms(source:pro2gram ,typedict:type2dict,last:int,result:seq.symdef, templates:pro2gram
  , dict:set.symbol,compiled:set.symbol) seq.symdef
     let a=  encoding:seq.encodingpair.symbol 
     if length.a=last   then result
    else 
    for  acc=result,   p=subseq(a,last+1,length.a) do
       let sym1=data.p
       if isspecial.sym1 /or isconst.sym1 
             /or name.module.sym1 /in "builtin internal $for $global" 
             /or name.sym1 /in "abort" then acc
       else
          let lr1 = getCode(source, data.p)
          let r=if (not.isempty.lr1 /or data.p /in compiled) then 
                 symdef(data.p,lr1) 
            else  if istype.data.p then
              symdef(data.p,deepcopybody(resulttype.data.p,typedict )) 
            else 
               let fx = handletemplate(dict, data.p, {org} print.data.p,  templates,compiled)
               let k = first.fx
               if length.fx=1 then
                 for paras=empty:seq.symbol,i=arithseq(nopara.k,1,1) do paras+Local.i /for( symdef(data.p,paras+k)) 
               else 
                assert length.fx > 1 report "KLJ??"+print.k+print.data.p
                    symdef(k,fx << 1) 
              acc+addsymbolref(data.p,r,typedict,dict,compiled) 
         /for(usedsyms(source, typedict,length.a,acc,templates,dict,compiled))
           
           
      function    addsymbolref(sym2:symbol,sd:symdef,typedict:type2dict , dict:set.symbol,compiled:set.symbol) symdef 
         let code=postbind3b(typedict,dict,sd, compiled)
         let discard=for acc2=symbolref.EqOp, sym=code    do  symbolref.sym /for(acc2)
            symdef(sym2,code )
            
            
/Function findabstract(all:set.passsymbols, s:symbol)seq.findabstractresult
let a = findelement(passsymbols(module.s, empty:set.symbol, empty:set.symbol, empty:set.symbol, empty:set.modref, empty:set.mytype, empty:seq.symtextpair)
, all
)
if isempty.a then empty:seq.findabstractresult
 else
  for acc = empty:seq.findabstractresult, e = toseq.defines.a_1 do
   if name.e = name.s ∧ nopara.e = nopara.s  then
      let z= for Tis=type? ,  idx=1,   t= types.e do
             let S=solveT(t,(types.s)_idx) 
             if S=type? then 
              {assert t=(types.s)_idx report "XXXXX"+print.t+print.(types.s)_idx}
             next(Tis,idx+1) else next(S,idx+1)
            /for(Tis)
    if  ?2(s,replaceTsymbol(z, e)) =EQ  then
       if s ? e =EQ /or isunbound.e then acc else
       acc + findabstractresult(e,z)
    else acc
   else acc
  /for(acc) 
  

  
  
  function solveT ( a:mytype,b:mytype) mytype
    if a=typeT then b
    else if isabstract.a  /and abstracttype.a=abstracttype.b then solveT(parameter.a,parameter.b)
    else type?
           
       
    {    function handletemplatesX(toprocess:seq.symdef,insource:set.symdef,templates:pro2gram,typedict:type2dict,compiled:set.symbol
        ,dict:set.symbol) set.symdef
          for source=insource,new=empty:seq.symdef,  p=toprocess do  
           let newones= for acc=empty:seq.symdef,  sym1=toseq.asset.code.p do 
           if isspecial.sym1 /or isconst.sym1 
             /or name.module.sym1 /in "builtin internal $for $global" 
             /or name.sym1 /in "abort" then acc
             else
              let isdefined=not.isempty.findelement(symdef(sym1,empty:seq.symbol),source) /or sym1 /in compiled
              if isdefined then acc
              else  if istype.sym1 then
                acc+symdef(sym1,deepcopybody(resulttype.sym1,typedict ))
              else 
               let fx =  getCode(templates, sym1)
               acc+if isempty.fx then 
                assert false report "J"+print.sym1
             symdef(sym1,for paras=empty:seq.symbol,i=arithseq(nopara.sym1,1,1) do paras+Local.i /for(paras+sym1))
               else symdef(sym1,fx )
         /for(acc)
           next(source /cup asset.newones,new+newones)
        /for( 
                 if isempty.new /or true then source else handletemplatesX(new,source,templates,typedict,compiled,dict))
         }
         
  use set.symdef    


Function postbind3b(typedict:type2dict, dict:set.symbol, sd:symdef, compiled:set.symbol) seq.symbol
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
       let newsym = replaceTsymbol(modpara, sym)
       if not.inmodule(sym,"builtin")then
            let t4= findelement(sym,compiled) 
            next(nextvar,map,result+if isempty.t4 then newsym else t4_1 )  
       else 
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
     ] )
       /for( result)
       
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

function deepcopysym(typedict:type2dict, type:mytype) symbol
 if type =typereal /or type=typeint then deepcopySym(type) else
 let z=flatwithtype(typedict,type)
 assert not.isempty.z report  "deepcopy cannot find type"+print.type+stacktrace
   deepcopySym(first.z)

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
