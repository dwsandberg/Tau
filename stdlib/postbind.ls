module postbind

use standard

use symbol 

use program

use seq.myinternaltype

use otherseq.mytype

use seq.mytype

use seq.symbol

use set.symbol

use otherseq.word

use seq.seq.mytype

Function postbind(alltypes:typedict, dict:set.symbol, roots:seq.symbol, theprg:program, templates:program)program
let root = symbol3("W","Wroot", typeint)
 postbindc(alltypes, dict, [ root], map(theprg, root, roots), templates, emptyprogram)

Function postbindc(alltypes:typedict, dict:set.symbol, toprocess:seq.symbol, sourceX:program, tempX:program, resultX:program)program
 if isempty.toprocess then resultX
 else
  for working = empty:set.symbol, result = resultX, source = sourceX, calls = empty:set.symbol, s = toprocess do
  let w = working + s
   if cardinality.w = cardinality.working ∨ isdefined.lookupcode(result, s)then next(w, result, source, calls)
   else
    let lr1 = lookupcode(source, s)
     { assert isdefined.lr1 report"postbind:expected to be defined:"+ print.s }
     let r = postbind3b(alltypes, dict, code.lr1,  s, source, tempX)
      next(w - s, if s = symbol3("W","Wroot", typeint) then result
      else map(result, s, code.r), sourceX.r, calls ∪ calls.r)
  /for(postbindc(alltypes, dict, toseq.calls, source, tempX, result))

type resultpb is calls:set.symbol, code:seq.symbol, sourceX:program

function postbind3b(alltypes:typedict, dict:set.symbol, code:seq.symbol, s:symbol, source:program, tempX:program)resultpb
let modpara=parameter.modname.s let org=print.s
 for result = empty:seq.symbol, calls = empty:set.symbol, sourceX = source, x = code do
  if isspecial.x then
  let a = if isSequence.x then Sequence(parameter.getbasetype(alltypes, replaceT(modpara, resulttype.x)), nopara.x)
  else if isstart.x then start.getbasetype(  alltypes, replaceT(modpara, resulttype.x))else x
   next(result + a, calls, sourceX)
  else
   let isfref = isFref.x
   let sym = basesym.x
    if isconst.sym ∨ inmodule(sym ,"$global") then next(result + x, calls, sourceX)
    else if inmodule(sym, "internal")  then next(result + x, calls + sym, sourceX)
    else if inmodule(sym, "$for")then next(result + replaceTsymbol(modpara, sym), calls, sourceX)
    else
     let lr1 = lookupcode(sourceX, sym)
     let newsym = if  not.iscomplex.modname.s ∨ isdefined.lr1 then sym else replaceTsymbol(modpara, sym)
     let xx4 = if newsym = sym then lr1 else { check to see if template already has been processed } lookupcode(sourceX, newsym)
      if isdefined.xx4 then
      let p2 = if isfref then [ Fref.target.xx4]
      else if"VERYSIMPLE"_1 ∈ getoption.code.xx4 then
       subseq(code.xx4, nopara.newsym + 1, length.code.xx4 - 2)
      else [ target.xx4]
       next(result + p2, calls + target.xx4, sourceX)
      else if inmodule(sym , "builtin") then
       if fsig.sym = "processresult(T process)"then
       let codeforbuiltin = [ Local.1]+   Fld(2,getbasetype(alltypes, parameter.modname.newsym)  ) 
        next(result + if isfref then Fref.newsym else newsym, calls + newsym, map(sourceX, newsym, codeforbuiltin))
       else if fsig.sym = "primitiveadd(int, T encodingpair)"then
       let encodingtype=typeref(moduleref."encoding","encoding")
       let encodingstatetype=typeref(moduleref."encoding","encodingstate")
       let encodingpairtype=typeref(moduleref."encoding","encodingpair")
       let addefunc = symbol3( addabstract( encodingtype, parameter.modname.newsym),"add"
       , [ addabstract(encodingstatetype, parameter.modname.newsym), addabstract( encodingpairtype, parameter.modname.newsym)]
       , addabstract(encodingstatetype, parameter.modname.newsym))
       let add2 =  symbol3(moduleref."internal","addencoding",  [ typeint, typeptr, typeint, typeint], typeint)
       let dc = deepcopysym(alltypes, addabstract( encodingpairtype, parameter.modname.newsym))
       let codeforbuiltin = [ Local.1, Local.2, Fref.addefunc, Fref.dc, add2, Words."NOINLINE STATE", Optionsym]
        next(result + if isfref then Fref.newsym else newsym, calls + newsym, map(sourceX, newsym, codeforbuiltin))
       else if fsig.sym = "getinstance:encodingstate.T"then
       let get = symbol3("internal","getinstance" , typeint  ,typeptr)
       let codeforbuiltin = encodenocode.parameter.modname.newsym + [ get, Words."NOINLINE STATE", Optionsym]
        next(result + if isfref then Fref.newsym else newsym, calls + newsym, map(sourceX, newsym, codeforbuiltin))
       else
        let p2 = codeforbuiltin(alltypes, length.result > 0, newsym, sym, modpara)
         next(result + p2, calls, sourceX)
      else if istype.sym then
      let p2 = definedeepcopy(alltypes, resulttype.newsym, org)
       next(result + if isfref then Fref.newsym else newsym, calls + newsym, map(sourceX, newsym, p2))
      else
       let fx = handletemplate(dict, newsym, org, sourceX, tempX)
       let k = first.fx
       let newsource = if length.fx = 1 then sourceX else map(sourceX, k, fx << 1)
        next(result + if isfref then Fref.k else k, calls + k, newsource)
 /for(resultpb(calls, result, sourceX))

function buildconstructor(alltypes:typedict, addfld:seq.mytype, flds:seq.seq.mytype, flatflds:seq.mytype, fldno:int, j:int, subfld:int, result:seq.symbol)seq.symbol
 if fldno > length.flds then result + Record(addfld + flatflds)
 else
  let fldsubfields = flds_fldno
  let newflatflds = if j > length.flatflds then
   flatflds
   + for acc = empty:seq.mytype, @e = fldsubfields do acc + getbasetype(alltypes, @e)/for(acc)
  else flatflds
  let newresult = result
  + if length.fldsubfields = 1 then [ Local.fldno]else [ Local.fldno]  +Fld(subfld,newflatflds_j)
   if subfld = length.fldsubfields - 1 then
    buildconstructor(alltypes, addfld, flds, newflatflds, fldno + 1, j + 1, 0, newresult)
   else buildconstructor(alltypes, addfld, flds, newflatflds, fldno, j + 1, subfld + 1, newresult)

function handletemplate(dict:set.symbol, sym:symbol, org:seq.word, sourceX:program, tempX:program)seq.symbol
let fx = lookupcode(tempX, sym)
 if isdefined.fx then
  if isdefined.lookupcode(sourceX, sym)then [ sym]else [ sym] + code.fx
 else
  let k = lookupsymbol(dict,  sym)
   assert cardinality.k = 1 report"Cannot find template for" + print.sym   
   + "while processing"
   + org
    assert not(sym = k_1)report"ERR12" + print.sym + print.k_1
    let dd = lookupcode(sourceX, k_1)
     if isdefined.dd then [ k_1]
     else { handles parameterized unbound cases like ?(int arc, int arc)graph.int } handletemplate(dict, k_1, org, sourceX, tempX)

function buildcode(acc:int, w:word)int
 acc * 2 + if w = first."real"then 1 else 0


function codeforbuiltin(alltypes:typedict, issequence:boolean, newsym:symbol, sym:symbol, modpara:mytype)seq.symbol
  if wordname.sym ∈ "offsets"then
  { symbol(offset(<rettype> <types with unknownsize >, <knowoffset> +"builtin", <rettype>)}
  let paratypes = paratypes.sym
  let offset = for acc = toint.(module.sym)_1, @e = subseq(paratypes, 2, length.paratypes)do
   acc + length.getsubflds(alltypes, replaceT(modpara, @e))
  /for(acc)
  let singlefld = 1 = length.getsubflds(alltypes, replaceT(modpara, resulttype.sym))
   if singlefld then Fld(offset, getbasetype( alltypes, replaceT(modpara, resulttype.sym)))+[Words."VERYSIMPLE", Optionsym]
   else [ Lit.offset,  symbol3("internal","GEP",  seqof.typeptr, typeint ,typeptr), Words."VERYSIMPLE", Optionsym]
 else if wordname.sym ∈ "build"then
 let c = for acc = empty:seq.seq.mytype, @e = paratypes.sym do acc + getsubflds(alltypes, replaceT(modpara, @e))/for(acc)
  buildconstructor(alltypes, if issequence then { for seq index func } [ typeint]else empty:seq.mytype, c, empty:seq.mytype, 1, 1, 0, empty:seq.symbol)
   else if fsig.sym = "packed(T seq)"then [ blocksym.getbasetype(alltypes,(paratypes.newsym)_1)]
 else if fsig.sym =" _(T seq, index)"then    
  let seqtype = getbasetype(alltypes,first.paratypes.newsym )
 [  symbol3( "internal","indexseq45",     seqtype, typeint , seqeletype.seqtype)]
  else if fsig.sym =" indexseqnobounds(T seq, index)" then    
  let seqtype = getbasetype(alltypes,first.paratypes.newsym )
 [   symbol3("internal","indexseqnobounds",     seqtype, typeint , seqeletype.seqtype)]
 else if wordname.sym = "forexp"_1 then
 let paras = for acc = empty:seq.mytype, p = paratypes.newsym do acc + getbasetype(alltypes, p)/for(acc)
  [ symbol3(moduleref."builtin","forexp",  paras, last.paras)]
   else if wordname.sym = "createthreadY"_1 then
 let paras = for acc = empty:seq.mytype, p = paratypes.newsym do acc + getbasetype(alltypes, p)/for(acc)
  [  symbol3( moduleref(" builtin" ,parameter.resulttype.sym),"createthreadY",  paras, getbasetype(alltypes, resulttype.sym))]
 else if wordname.sym ∈ "assert"then
 let t = getbasetype(alltypes, parameter.modname.newsym)
  [abortsymbol.t]
  else if  wordname.sym ∈ "load "  then
       [Idx.getbasetype(alltypes, resulttype.newsym)]
 else if wordname.sym ∈ "setfld"then [ newsym]
 else if sym=symbol4(moduleref("builtin", typeT),"bitcast"_1,typeT,[typeptr],   seqof.typeT) then
  [ symbol3("internal","bitcast",typeptr,typeptr)]
 else if sym=symbol3(moduleref("builtin", typeT),"bitcast",seqof.seqof.typeT,seqof.typeT)  then
  [ symbol3("internal","bitcast",typeptr,typeptr)]
 else if fsig.sym = "toseqX:T(ptr)" ∨ fsig.sym = "bitcast(T)"
 ∨ fsig.sym = "bitcast(T blockseq)"then
 let t = getbasetype(alltypes, resulttype.newsym)
  [symbol4(moduleref."internal","toseq"_1,  t,[typeptr],t) ]
 else
  assert sym=symbol3(moduleref("builtin",typeT),"allocateseq:T",typeint,typeint,typeint,seqof.typeT) report"not expecting" + print.sym
      [replaceTsymbol(getbasetype(alltypes, resulttype.newsym),
      symbol4(moduleref."internal","allocateseq"_1,typeT,[typeint,typeint,typeint],typeT  ))]

   
 
   
   function blocksym(  basetype:mytype)symbol
     let p= parameter.basetype 
     let p2=seqof.if p=typebyte /or p=typebit /or p=typeboolean then typeint else p
     symbol3("tausupport","blockIt", p2, p2)
     
 
function encodenocode(typ:mytype)seq.symbol
let gl = symbol4(moduleref."$global","global"_1 ,  typ,empty:seq.mytype,seqof.typeint )
let setfld =  symbol3(moduleref("builtin",typeint),"setfld",[typeint, seqof.typeint, typeint], typeint)
let encodenosym =  symbol3("tausupport","encodingno",   seqof.typeword , typeint)
 if typ = typeref(moduleref."tausupport","typename" ) then [ Lit.0, gl, Lit.2, setfld, Define."xx",gl]+Fld(0,typeint) 
 else if typ = seqof.typeref(moduleref."?","char")then
  [ Lit.0, gl, Lit.1, setfld, Define."xx", gl]+Fld(0,typeint) 
 else
  ifthenelse([ gl]+Fld( 0,typeint)+[ Lit.0, EqOp], [ Lit.0, gl, Words.typerep.typ, encodenosym, setfld, Define."xx", gl ]+Fld(0,typeint), [ gl]+Fld(0,typeint) , typeint)

function definedeepcopy(alltypes:typedict, type:mytype, org:seq.word)seq.symbol
 if type=typeint /or type=typeword  /or isencoding.type  then [ Local.1]
 else if isseq.type   then
 let basetype = getbasetype(alltypes, type)
  if  basetype =typeint /or basetype=typereal /or basetype=typeboolean  then [ Local.1, blocksym( basetype)]
  else
   let cat =  symbol3(type, "+",  [ type, parameter.type], type)
   let resulttype = basetype
   let elementtype = parameter.basetype
   let element = symbol3(moduleref("$for", elementtype),"element",  empty:seq.mytype, elementtype)
   let acc =  symbol3(moduleref("$for", typeptr),"acc",  empty:seq.mytype, typeptr)
     Emptyseq.elementtype
    + [ Local.1, acc, element, acc, element, deepcopysym(alltypes, parameter.type), cat, Littrue, acc,  symbol3( moduleref("builtin",typeint),"forexp", [ resulttype, resulttype, resulttype, elementtype, typeptr, typeboolean, resulttype], resulttype)
    ]
    + blocksym(  basetype)
 else
  let subflds = getsubflds(alltypes, type)
  let y = subfld(alltypes, subflds, 1, empty:seq.mytype, empty:seq.symbol)
   if length.subflds = 1 then
    { only one element in record so type is not represent by actual record } [ Local.1]
    + subseq(y, 4, length.y - 1)
   else y

function subfld(alltypes:typedict, flds:seq.mytype, fldno:int, fldkinds:seq.mytype, result:seq.symbol)seq.symbol
 if fldno > length.flds then result + [ Record.fldkinds]
 else
  let fldtype = flds_fldno
  let kind = getbasetype(alltypes, fldtype)
   subfld(alltypes, flds, fldno + 1, fldkinds + kind, result + [ Local.1]+Fld( fldno - 1,kind)+ deepcopysym(alltypes, fldtype))