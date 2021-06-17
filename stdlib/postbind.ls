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

use set.symdef

use worddict.seq.symbol
 
 use seq.seq.symbol

Function postbind(alltypes:typedict, dict:set.symbol, roots:seq.symbol, theprg:program, templates:program)program
let root = symbol(moduleref."W","Wroot", typeint)
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
     let r = postbind3b(alltypes, dict, code.lr1, s, source, tempX)
     next(w - s, if s = symbol(moduleref."W","Wroot", typeint)then result else map(result, s, code.r), sourceX.r, calls ∪ calls.r)
  /for(postbindc(alltypes, dict, toseq.calls, source, tempX, result))

type resultpb is calls:set.symbol, code:seq.symbol, sourceX:program

Function Fld(offset:int, type:mytype)seq.symbol [ Lit.offset, Load.type]

function postbind3b(alltypes:typedict, dict:set.symbol, code:seq.symbol, s:symbol, source:program, tempX:program)resultpb
let modpara = para.module.s
let org = print.s
 for result = empty:seq.symbol, calls = empty:set.symbol, sourceX = source, x = code do
  if isspecial.x then
  let a = if isSequence.x then Sequence(parameter.getbasetype(alltypes, replaceT(modpara, resulttype.x)), nopara.x)
  else if isstart.x then Start.getbasetype(alltypes, replaceT(modpara, resulttype.x))else x
   next(result + a, calls, sourceX)
  else
   let isfref = isFref.x
   let sym = basesym.x
    if isconst.sym ∨ inmodule(sym,"$global")then next(result + x, calls, sourceX)
    else if inmodule(sym,"internal")then next(result + x, calls + sym, sourceX)
    else if inmodule(sym,"$for")then next(result + replaceTsymbol(modpara, sym), calls, sourceX)
    else
     let lr1 = lookupcode(sourceX, sym)
     let newsym = if issimple.module.s ∨ isdefined.lr1 then sym else replaceTsymbol(modpara, sym)
     let xx4 = if newsym = sym then lr1 else { check to see if template already has been processed }lookupcode(sourceX, newsym)
     if isdefined.xx4 then
      let p2 = if isfref then [ Fref.target.xx4]
      else if"VERYSIMPLE"_1 ∈ getoption.code.xx4 then
       subseq(code.xx4, nopara.newsym + 1, length.code.xx4 - 2)
      else [ target.xx4]
      next(result + p2, calls + target.xx4, sourceX)
      else if inmodule(sym,"builtin")then
       if wordname.sym ∈ "processresult"then
       let codeforbuiltin = [ Local.1] + Fld(2, getbasetype(alltypes, para.module.newsym))
       next(result + if isfref then Fref.newsym else newsym, calls + newsym, map(sourceX, newsym, codeforbuiltin))
       else if wordname.sym ∈ "primitiveadd"then
       let encodingtype = typeref."encoding encoding. "
       let encodingstatetype = typeref."encodingstate encoding. "
       let encodingpairtype = typeref."encodingpair encoding. "
       let addefunc = symbol(moduleref("encoding", para.module.newsym),"add", [ addabstract(encodingstatetype, para.module.newsym), addabstract(encodingpairtype, para.module.newsym)], addabstract(encodingstatetype, para.module.newsym))
       let add2 = symbol(internalmod,"addencoding", [ typeint, typeptr, typeint, typeint], typeint)
       let dc = deepcopysym(alltypes, addabstract(encodingpairtype, para.module.newsym))
       if true then
        let codeforbuiltin = [ Local.1, Local.2, Fref.addefunc, Fref.dc, add2, Words."NOINLINE STATE", Optionsym]
        next(result + if isfref then Fref.newsym else newsym, calls + newsym, map(sourceX, newsym, codeforbuiltin))
        else next(result + [ Fref.addefunc, Fref.dc, add2], calls + addefunc, sourceX)
       else if wordname.sym ∈ "getinstance"then
       let get = symbol(internalmod,"getinstance", typeint, typeptr)
       next(result + encodenocode.para.module.newsym + [ get], calls, sourceX)
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
  + if length.fldsubfields = 1 then [ Local.fldno]else [ Local.fldno] + Fld(subfld, newflatflds_j)
  if subfld = length.fldsubfields - 1 then
    buildconstructor(alltypes, addfld, flds, newflatflds, fldno + 1, j + 1, 0, newresult)
   else buildconstructor(alltypes, addfld, flds, newflatflds, fldno, j + 1, subfld + 1, newresult)

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

function buildcode(acc:int, w:word)int
 acc * 2 + if w = first."real"then 1 else 0
 
 Function baseoffset(sym:symbol) int toint.abstracttype.para.module.sym 

Function getsubflds(d:typedict, type:mytype)seq.mytype
 if type = typeint ∨ type = typereal ∨ type = typeptr then [ type]
 else
  { if type = typeboolean then typeinfo.[ typeboolean]else }
  if isseq.type   then  [ typeptr]
  else
   let t = findtype(d, type)
    assert length.t = 1 report"type not found" + print.type + stacktrace
     subflds.t_1
     
function codeforbuiltin(alltypes:typedict, issequence:boolean, newsym:symbol, sym:symbol, modpara:mytype)seq.symbol
 if wordname.sym ∈ "offsets"then
  { symbol(offset(<rettype> <types with unknownsize >, <knowoffset> +"builtin", <rettype>)}
  let paratypes = paratypes.sym
  let offset = for acc = baseoffset.sym, @e = subseq(paratypes, 2, length.paratypes)do
   acc + length.getsubflds(alltypes, replaceT(modpara, @e))
  /for(acc)
  let singlefld = 1 = length.getsubflds(alltypes, replaceT(modpara, resulttype.sym))
  if singlefld then Fld(offset, getbasetype(alltypes, replaceT(modpara, resulttype.sym))) + [ Words."VERYSIMPLE", Optionsym]
   else [ Lit.offset, symbol(internalmod,"GEP", seqof.typeptr, typeint, typeptr), Words."VERYSIMPLE", Optionsym]
 else if wordname.sym ∈ "build"then
 let c = for acc = empty:seq.seq.mytype, @e = paratypes.sym do acc + getsubflds(alltypes, replaceT(modpara, @e))/for(acc)
 buildconstructor(alltypes, if issequence then { for seq index func }[ typeint]else empty:seq.mytype, c, empty:seq.mytype, 1, 1, 0, empty:seq.symbol)
 else if wordname.sym ∈ "packed"then [ blocksym.getbasetype(alltypes,(paratypes.newsym)_1)]
 else if wordname.sym ∈ "_"then
 let seqtype = getbasetype(alltypes, first.paratypes.newsym)
 [ symbol(internalmod,"indexseq45", seqtype, typeint, parameter.seqtype)]
 else if wordname.sym = "forexp"_1 then
 let paras = for acc = empty:seq.mytype, p = paratypes.newsym do
  acc + if"$base"_1 ∈ print.p then p else getbasetype(alltypes, p)
 /for(acc)
 [ symbol(moduleref."builtin","forexp", paras, last.paras)]
 else if wordname.sym = "createthreadY"_1 then
 let paras = for acc = empty:seq.mytype, p = paratypes.newsym do acc +  coretype(p,type2dict(alltypes) )/for(acc)
 [ symbol(moduleref("builtin", parameter.resulttype.sym),"createthreadY", paras, getbasetype(alltypes, resulttype.sym))]
 else if wordname.sym ∈ "assert"then
 let t = getbasetype(alltypes, para.module.newsym)
 [ abortsymbol.t]
 else if wordname.sym ∈ "load"then [ Load.coretype( resulttype.newsym,type2dict(alltypes))]
 else if sym = symbol4(moduleref("builtin", typeT),"bitcast"_1, typeT, [ typeptr], seqof.typeT)then
  [ symbol(internalmod,"bitcast", typeptr, typeptr)]
 else if sym = symbol(moduleref("builtin", typeT),"bitcast", seqof.seqof.typeT, seqof.typeT)then
  [ symbol(internalmod,"bitcast", typeptr, typeptr)]
 else
  assert wordname.sym ∈ "bitcast toseqX"report"not expecting" + print.sym
  let t = getbasetype(alltypes, resulttype.newsym)
  [ symbol4(internalmod,"toseq"_1, t, [ typeptr], t)]
  
use pro2gram

function blocksym(basetype:mytype)symbol
let p = parameter.basetype
let p2 = seqof.if p = typebyte ∨ p = typebit ∨ p = typeboolean then typeint else p
 symbol(moduleref."tausupport","blockIt", p2, p2)

function encodenocode(typ:mytype)seq.symbol
let gl = symbol4(moduleref."$global","global"_1, typ, empty:seq.mytype, seqof.typeint)
let set = symbol(moduleref."tausupport","set", [ typeptr, typeint], typeptr)
let encodenosym = symbol(moduleref."tausupport","encodingno", seqof.typeword, typeint)
if typ = typeref."typename tausupport. "then [ Lit.2]
 else if typ = seqof.typeref."char UTF8."then [ Lit.1]
 else
  ifthenelse([ gl] + Fld(0, typeint) + DefineF."X1"_1
  + [ LocalF("X1",typeint), Lit.0, EqOp], [ gl, Words.print.typ, encodenosym, set, DefineF."xx"_1, gl] + Fld(0, typeint), [ LocalF("X1",typeint)], typeint)

function definedeepcopy(alltypes:typedict, type:mytype, org:seq.word)seq.symbol
 if type = typeint ∨ type = typeword ∨ isencoding.type then [ Local.1]
 else if isseq.type then
 let basetype = getbasetype(alltypes, type)
 if basetype = typeint ∨ basetype = typereal ∨ basetype = typeboolean then [ Local.1, blocksym.basetype]
  else
   let cat = symbol(tomodref.type,"+", [ type, parameter.type], type)
   let resulttype = basetype
   let elementtype = parameter.basetype
   let element = symbol(moduleref("$for", elementtype),"element", empty:seq.mytype, elementtype)
   let acc = symbol(moduleref("$for", typeptr),"acc", empty:seq.mytype, typeptr)
   Emptyseq.elementtype
    + [ Local.1, acc, element, acc, element, deepcopysym(alltypes, parameter.type), cat, Littrue, acc, symbol(moduleref("builtin", typeint),"forexp", [ resulttype, resulttype, resulttype, elementtype, typeptr, typeboolean, resulttype], resulttype)
    ]
    + blocksym.basetype
 else
  let subflds = getsubflds(alltypes, type)
  let y = subfld(alltypes, subflds, 1, empty:seq.mytype, empty:seq.symbol)
  if length.subflds = 1 then
    { only one element in record so type is not represent by actual record }[ Local.1]
    + subseq(y, 4, length.y - 1)
   else y

function subfld(alltypes:typedict, flds:seq.mytype, fldno:int, fldkinds:seq.mytype, result:seq.symbol)seq.symbol
 if fldno > length.flds then result + [ Record.fldkinds]
 else
  let fldtype = flds_fldno
  let kind = getbasetype(alltypes, fldtype)
  subfld(alltypes, flds, fldno + 1, fldkinds + kind, result + [ Local.1] + Fld(fldno - 1, kind) + deepcopysym(alltypes, fldtype)) 
  
  Function getbasetype(d:typedict,intype:mytype) mytype
{ base types are int real boolean ptr seq.int seq.real seq.boolean seq.ptr seq.byte seq.bit 
   seq.packed2 seq.packed3 seq.packed4 seq.packed5 seq.packed6 or $base.x where x is a integer}
   { if abstracttypeof.intype = typeref ( "$base $base .") then { used for type of next in for expression } intype
 else if isseq.intype then
     seqof.coretype(parameter.intype,type2dict(d),6)
   else coretype(intype,type2dict(d)  )
 }
  if abstracttypeof.intype = typeref ( "$base $base .") then { used for type of next in for expression } intype
 else if isencoding.intype  then  typeint
     else
  let isseq =  isseq.intype 
  let type= if isseq then parameter.intype else intype
  if  type ∈ packedtypes then 
     if isseq then intype else typeptr
  else  if  type ∈ [typeint, typeboolean ,typereal, typeptr]then 
     if isseq then intype else type
  else if  type   ∈ [ typebit, typebyte ] then 
    if isseq then  intype else typeint
  else if isseq.type  /and isseq then seqof.typeptr
  else 
   let t = findtype(d, type)
   assert length.t = 1 report"type not found" + print.type + stacktrace
   let size = length.subflds.t_1
     if size > 1 then
     if not.isseq then typeptr
     else if size = 2 then seqof.typeref(  "packed2 tausupport .")
     else if size = 3 then seqof.typeref(  "packed3  tausupport .")
     else if size = 4 then seqof.typeref(  "packed4  tausupport .")
     else if size = 5 then seqof.typeref(  "packed5  tausupport .")
     else if size = 6 then seqof.typeref(  "packed6  tausupport .")  
     else seqof.typeptr
    else
     let basetype =(subflds.t_1)_1
      if isseq.basetype   /and isseq  then seqof.typeptr
       else let basetype2=getbasetype(d,basetype)
         if not.isseq then basetype2
         else    if isseq.basetype2     then seqof.typeptr
         else seqof.basetype2 
         
 Function  prescan(   prg:pro2gram) pro2gram 
      for  acc=empty:set.symdef ,  p=tosymdefs.prg do
      let pdict = for pmap = emptyworddict:worddict.seq.symbol, parano = 1, e = constantseq(10000, 1)
      while parano ≤ nopara.sym.p  do next(add(pmap, toword.parano, [ Local.parano]), parano + 1)/for(pmap)
        for  result = empty:seq.symbol, nextvar = nopara.sym.p+1, map = pdict, sym = code.p do
   if not.isempty.result ∧ last.result = PreFref then
              next(  result >> 1+Fref.sym,nextvar, map)
           else if islocal.sym then
             let t = lookup(map, wordname.sym)
             next(  result + if isempty.t then [ sym]else t_1, nextvar, map)
           else if isparameter.sym then
               let sym2 = Local.value.sym
               let t = lookup(map, wordname.sym2)
               if isempty.t then next(  result + if isempty.t then [ sym]else t_1, nextvar, map)
                  else next(  result + t_1, nextvar, map)
           else if isdefine.sym then
               let thelocal = wordname.sym
               let len=length.result
    if len > 0 ∧ (isconst.result_len ∨ islocal.result_len)then
     next(  subseq(result, 1, length.result - 1), nextvar, replace(map, thelocal, [ result_len]))
    else next( result + Define.nextvar, nextvar + 1, replace(map, thelocal, [ Local.nextvar]))
   else if isloopblock.sym then
   let nopara = nopara.sym
   let addlooplocals = for pmap = map, parano = 1, e = constantseq(10000, 1)while parano ≤ nopara do next(replace(pmap, toword(firstvar.sym + parano - 1), [ Local(nextvar + parano - 1)]), parano + 1)/for(pmap)
   next(  result + Loopblock(paratypes.sym, nextvar, resulttype.sym), nextvar + nopara, addlooplocals)
   else next(result + sym, nextvar, map)
      /for(acc+symdef( sym.p,result))
      /for(pro2gram.acc)         
