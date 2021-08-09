module postbind

use standard

use symbol

use program
 
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

use seq.findabstractresult 

use passsymbol

 function usedsyms(source:program ,typedictin:type2dict,last:int,result:seq.symdef, templates:program
  , dict:set.symbol,compiled:set.symbol,typeflds:seq.seq.mytype) seq.symdef
     let a=  encoding:seq.encodingpair.symbol 
     if length.a=last   then result
    else 
    let typedict={buildtypedict(asset.result,typeflds)}typedictin
    for  acc=result,   p=subseq(a,last+1,length.a) do
       let sym=data.p
       if isspecial.sym /or isconst.sym 
             /or name.module.sym /in "builtin internal $for $global" 
              then acc
       else
          let lr1 = getCode(source, sym)
          let sd=if (not.isempty.lr1 /or sym /in compiled) then 
                 symdef(sym,lr1) 
            else  if istype.sym then
              symdef(sym,deepcopybody(resulttype.sym,typedict )) 
            else  
              let sym2=if isunbound.sym then
                 let k2=      lookupbysig(data.source,sym)
                { assert not.isempty.k2 /or print.sym /in [ "seq.seq.word:=(seq.word, seq.word)boolean"
                 ,"otherseq.seq.alphaword:?(seq.alphaword, seq.alphaword)ordering"
                 ,"set.encoding.seq.char:?(encoding.seq.char, encoding.seq.char)ordering" 
                 report "HK"+print.sym}
                let k = lookupsymbol(dict, sym) 
               assert cardinality.k = 1 report"Cannot bind unbound"   + print.sym  
               assert sym ≠ k_1 report"ERR12" + print.sym + print.k_1
                 k_1 else sym
               if   issimple.module.sym2 /or sym2 /in compiled then 
                    for paras=empty:seq.symbol,i=arithseq(nopara.sym2,1,1) do paras+Local.i /for (symdef(sym2,  paras+sym2))
               else  
                 let gx=findabstract(templates,sym2)
                   assert length.gx = 1 report"Cannot find template for" + print.sym2  
                  for newcode=empty:seq.symbol,sym4 = code.sd.gx_1 do   newcode+ replaceTsymbol(modpara.gx_1, sym4)
                 /for(symdef(  sym2 ,    newcode))     
         let newsd=postbind(sd,typedict,  compiled)
         let discard=for acc2=symbolref.EqOp, sym5=code.newsd  do  symbolref.sym5 /for(acc2)
            acc+symdef(sym ,code.newsd )    
         /for(usedsyms(source, typedict,length.a,acc,templates,dict,compiled,typeflds))    
         
         Function lookupsymbol(dict:set.symbol, sym:symbol)set.symbol  findelement2(dict, sym)
         
           if issimple.module.sym /or para.module.sym=typeT then 
            findelement2(dict, sym)
           else 
              assert false report "JKLS"+print.sym
            findelement2(dict, sym)


Function postbind(sd:symdef,typedict:type2dict,   compiled:set.symbol) symdef
let modpara = para.module.sym.sd
 let pdict = for pmap = empty:intdict.seq.symbol, parano = 1, e = constantseq(10000, 1)while parano ≤ nopara.sym.sd do 
               next(add(pmap, parano, [ Local.parano]), parano + 1)
            /for(pmap)
for nextvar = nopara.sym.sd + 1, map = pdict,result = empty:seq.symbol ,  symx = code.sd do
         let sym = replaceTsymbol(modpara, symx)
     if name.module.sym ∈ "$define"then
      next(nextvar + 1, replace(map, value.sym, [ Local.nextvar]),   result + Define.nextvar)
     else if name.module.sym ∈ "$local"then
       let t = lookup(map, value.sym)
        next(nextvar, map,   result + t_1)  
     else  if isspecial.sym then
     let p2 = if isSequence.sym then Sequence(parameter.basetype(   resulttype.sym,typedict), nopara.sym)
            else if isstart.sym then Start.basetype(  resulttype.sym,typedict)
          else sym
       next(nextvar,map,result + p2 )
    else if isconst.sym ∨ inmodule(sym,"$global") ∨ inmodule(sym,"internal") /or sym=PreFref /or sym= Optionsym then 
       next(nextvar,map,result + sym)
    else if inmodule(sym,"$for")then next(nextvar,map,result + sym )
    else 
       if not.inmodule(sym,"builtin")then
            let t4= findelement(sym,compiled) 
            next(nextvar,map,result+if isempty.t4 then sym else t4_1 )  
       else 
         if  name.sym ∈ "primitiveadd" then
        let encodingtype = typeref."encoding encoding. "
       let encodingstatetype = typeref."encodingstate encoding. "
       let encodingpairtype = typeref."encodingpair encoding. "
       let addefunc = symbol(moduleref("encoding", para.module.sym),"add", [ addabstract(encodingstatetype, para.module.sym), addabstract(encodingpairtype, para.module.sym)], addabstract(encodingstatetype, para.module.sym))
       let add2 = symbol(internalmod,"addencoding", [ typeint, typeptr, typeint, typeint], typeint)
       let dc = deepcopySym(  addabstract(encodingpairtype, para.module.sym))
         next(nextvar+1,map,result+[ PreFref,addefunc, PreFref,dc, add2] )
      else if name.sym ∈ "getinstance"then
          let get = symbol(internalmod,"getinstance", typeint, typeptr)
            next(nextvar+2,map,result + encodenocode(para.module.sym,nextvar) +   get  )
        else  next(nextvar,map   
      ,    if name.sym ∈ "pushflds" then
            if iscoretype.para.module.sym then result
            else 
             let t = flatflds(typedict,para.module.sym)
             if isempty.t /or typeT ∈ t  then 
                    result+sym
             else if length.t=1  then result
             else 
              for newresult=result >> 1 , idx=0, x=t do
                 next(newresult+ [last.result,Lit.idx,Getfld.x],idx+1)
              /for(newresult) 
      else  if name.sym ∈ "buildrecord" then
        let t = flatflds(typedict,para.module.sym)
        result+if isempty.t /or typeT ∈ t then sym  else  Record.t
    else  if name.sym ∈  "bitcast"  then
     let a = coretype(first.paratypes.sym, typedict)
      let b = coretype(resulttype.sym, typedict)
      if a = b then result else   result + symbol(internalmod,"bitcast", a, b)
    else result+  if name.sym ∈ "processresult"then
            [ Lit.2 , Getfld.coretype( para.module.sym,typedict )]
   else [ if name.sym ∈ "typesize"then
       let typ=para.module.sym
          if typ = typeint ∨ typ = typereal ∨ typ = typeptr /or isseq.typ then Lit.1
              else       let t = flatflds(typedict,typ)  
        if isempty.t /or typeT ∈ t then sym else Lit.length.t
  else     if name.sym ∈ "length"then  GetSeqLength
else if name.sym ∈ "packed"then 
 let typ=seqof.coretype(para.module.sym, typedict)
          symbol(moduleref( "tausupport"),"blockIt", typ,typ)
     else if name.sym ∈ "aborted"then   symbol(internalmod,"aborted", typeptr, typeboolean)
 else if name.sym ∈ "assert "  then
      abortsymbol.coretype(para.module.sym, typedict)
        else if name.sym ∈ "_"then
     let seqtype = basetype(first.paratypes.sym,typedict)
          symbol(internalmod,"indexseq45", seqtype, typeint,  parameter.seqtype )
       else if name.sym ∈ "getseqtype"then   GetSeqType
      else if name.sym ∈ "set"then
         setSym.coretype(para.module.sym, typedict)
      else if name.sym = "forexp"_1 then  
  let paras = for acc = empty:seq.mytype, p = paratypes.sym do
  acc + if"$base"_1 ∈ print.p then p else  basetype( p,typedict)
 /for(acc)
  symbol(moduleref."builtin","forexp", paras, last.paras)
      else  if name.sym = "createthreadY"_1 then
        let paras = for paras = empty:seq.mytype, p = paratypes.sym do paras + coretype(p, typedict)/for(paras)
       let rt = processof.coretype( parameter.resulttype.sym , typedict)
        symbol(builtinmod.rt,"createthreadY", paras, typeptr)
       else if name.sym ∈ "fld getfld"then
            let typ=resulttype.sym  
            if iscoretype.typ then  Getfld.typ  
            else if isabstract.typ then sym 
            else
            let a=flatflds( typedict,typ)
            assert not.isempty.a report "cannot find type getfld" +print.typ
            if length.a > 1 then 
              symbol(internalmod,"GEP", seqof.typeptr, typeint, typeptr)
            else   Getfld.first.a  
        else if name.sym ∈ "empty" then Sequence(coretype(para.module.sym, typedict),0)
  else
        assert name.sym /in "offsets build" report "post bind"+print.sym
     sym
     ] )
   /for(symdef( sym.sd , result))
       
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

use typerep


use mytype

      use seq.seq.mytype
      
        use set.symdef    



/function buildcode(acc:int, w:word)int
 acc * 2 + if w = first."real"then 1 else 0
 
 
{ base types are int real boolean ptr seq.int seq.real seq.boolean seq.ptr seq.byte seq.bit 
   seq.packed2 seq.packed3 seq.packed4 seq.packed5 seq.packed6 or $base.x where x is a integer}
            
Function  prescan2(   prg:program) program 
      for  acc=empty:set.symdef ,  p=tosymdefs.prg do
         for  result = empty:seq.symbol, sym = code.p do
          {if not.isempty.result ∧ last.result = PreFref then
               result >> 1+Fref.sym
           else} if  islocal.sym then
                 result +  Local.value.sym
           else if isdefine.sym then  result+Define.value.sym
           else result + sym
      /for(acc+symdef( sym.p,result))
      /for(program.acc)      
      
Function postbind(alltypes:type2dict, dict:set.symbol, roots:seq.symbol, theprg:program, 
templates:program,compiled:set.symbol,typeflds:seq.seq.mytype)program
let root = symbol(moduleref."W","Wroot", typeint)
   let discard=for acc=0 ,r=roots do let discard2=encode.r 0 /for(0)
 program.asset.usedsyms(theprg,alltypes,0,empty:seq.symdef,templates,dict,compiled,typeflds)
  
          
