module postbind

use standard

use symbol

use seq.myinternaltype

use otherseq.mytype

use seq.mytype

use seq.symbol

use set.symbol

use otherseq.word

use seq.seq.mytype

Function postbind(alltypes:typedict, dict:set.symbol, roots:seq.symbol, theprg:program, templates:program)program
let root = newsymbol("Wroot", typeref(moduleref."W","W"), empty:seq.mytype, typeint)
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
     let r = postbind3b(alltypes, dict, code.lr1, parameter.modname.s, print.s, source, tempX)
      next(w - s, if s = newsymbol("Wroot", typeref(moduleref."W","W"), empty:seq.mytype, typeint)then result
      else map(result, s, code.r), sourceX.r, calls ∪ calls.r)
  /for(postbindc(alltypes, dict, toseq.calls, source, tempX, result))

type resultpb is calls:set.symbol, code:seq.symbol, sourceX:program

function postbind3b(alltypes:typedict, dict:set.symbol, code:seq.symbol, modpara:mytype, org:seq.word, source:program, tempX:program)resultpb
let coretypes = false
 for result = empty:seq.symbol, calls = empty:set.symbol, sourceX = source, x = code do
  if isspecial.x then
  let a = if isSequence.x then Sequence(parameter.getbasetype(alltypes, replaceT(modpara, resulttype.x)), nopara.x)
  else if isstart.x then start.getbasetype(coretypes, alltypes, replaceT(modpara, resulttype.x))else x
   next(result + a, calls, sourceX)
  else
   let isfref = isFref.x
   let sym = basesym.x
    if isconst.sym ∨ inmodule(sym ,"$global") then next(result + x, calls, sourceX)
    else if module.sym = "builtin"then next(result + x, calls + sym, sourceX)
    else if inmodule(sym, "$for")then next(result + replaceTsymbol(modpara, sym), calls, sourceX)
    else
     let lr1 = lookupcode(sourceX, sym)
     let newsym = if isempty.typerep.modpara ∨ isdefined.lr1 then sym else replaceTsymbol(modpara, sym)
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
       let addefunc = newsymbol("add", addabstract( encodingtype, parameter.modname.newsym)
       , [ addabstract(encodingstatetype, parameter.modname.newsym), addabstract( encodingpairtype, parameter.modname.newsym)]
       , addabstract(encodingstatetype, parameter.modname.newsym))
       let add2 = newsymbol("addencoding", moduleref."builtin", [ typeint, typeptr, typeint, typeint], typeint)
       let dc = deepcopysym(alltypes, addabstract( encodingpairtype, parameter.modname.newsym))
       let codeforbuiltin = [ Local.1, Local.2, Fref.addefunc, Fref.dc, add2, Words."NOINLINE STATE", Optionsym]
        next(result + if isfref then Fref.newsym else newsym, calls + newsym, map(sourceX, newsym, codeforbuiltin))
       else if fsig.sym = "getinstance:encodingstate.T"then
       let get = newsymbol("getinstance",moduleref."builtin" ,[typeint] ,typeptr)
       let codeforbuiltin = encodenocode.parameter.modname.newsym + [ get, Words."NOINLINE STATE", Optionsym]
        next(result + if isfref then Fref.newsym else newsym, calls + newsym, map(sourceX, newsym, codeforbuiltin))
       else
        let p2 = codeforbuiltin(alltypes, length.result > 0, newsym, sym, modpara)
         next(result + p2, calls, sourceX)
      else if subseq(name.sym, 1, 2) = "type:"then
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
  let k = lookup(dict, name.sym, paratypes.sym)
   assert cardinality.k = 1 report"Cannot find template for" + name.sym + "("
   + for acc ="", @e = paratypes.sym do list(acc,",", print.@e)/for(acc)
   + ")"
   + "while processing"
   + org
    assert not(sym = k_1)report"ERR12" + print.sym + print.k_1
    let dd = lookupcode(sourceX, k_1)
     if isdefined.dd then [ k_1]
     else { handles parameterized unbound cases like ?(int arc, int arc)graph.int } handletemplate(dict, k_1, org, sourceX, tempX)

function buildcode(acc:int, w:word)int
 acc * 2 + if w = first."real"then 1 else 0

function getbasetype(coretypes:boolean, alltypes:typedict, t:mytype)mytype
let a = getbasetype(alltypes, t)
 if length.typerep.a > 2 ∧ coretypes then typeptr else a

function codeforbuiltin(alltypes:typedict, issequence:boolean, newsym:symbol, sym:symbol, modpara:mytype)seq.symbol
let coretypes = false
 if(name.sym)_1 ∈ "offsets"then
  { symbol(offset(<rettype> <types with unknownsize >, <knowoffset> +"builtin", <rettype>)}
  let paratypes = paratypes.sym
  let offset = for acc = toint.(module.sym)_1, @e = subseq(paratypes, 2, length.paratypes)do
   acc + length.getsubflds(alltypes, replaceT(modpara, @e))
  /for(acc)
  let singlefld = 1 = length.getsubflds(alltypes, replaceT(modpara, resulttype.sym))
   if singlefld then Fld(offset, getbasetype(coretypes, alltypes, replaceT(modpara, resulttype.sym)))+[Words."VERYSIMPLE", Optionsym]
   else [ Lit.offset, newsymbol("GEP",moduleref."internal",[seqof.typeptr, typeint],typeptr), Words."VERYSIMPLE", Optionsym]
 else if(name.sym)_1 ∈ "build"then
 let c = for acc = empty:seq.seq.mytype, @e = paratypes.sym do acc + getsubflds(alltypes, replaceT(modpara, @e))/for(acc)
  buildconstructor(alltypes, if issequence then { for seq index func } [ typeint]else empty:seq.mytype, c, empty:seq.mytype, 1, 1, 0, empty:seq.symbol)
   else if fsig.sym = "packed(T seq)"then [ blocksym(alltypes,(paratypes.newsym)_1)]
 else if fsig.sym =" _(T seq, index)"then    
  let seqtype = getbasetype(alltypes,first.paratypes.newsym )
 [  newsymbol("indexseq45", moduleref."builtin", [  seqtype, typeint], seqeletype.seqtype)]
  else if fsig.sym =" indexseqnobounds(T seq, index)" then    
  let seqtype = getbasetype(alltypes,first.paratypes.newsym )
 [  newsymbol("indexseqnobounds", moduleref."builtin", [  seqtype, typeint], seqeletype.seqtype)]
 else if(name.sym)_1 = "forexp"_1 then
 let paras = for acc = empty:seq.mytype, p = paratypes.newsym do acc + getbasetype(alltypes, p)/for(acc)
  [ newsymbol("forexp", moduleref."builtin", paras, last.paras)]
   else if(name.sym)_1 = "createthreadY"_1 then
 let paras = for acc = empty:seq.mytype, p = paratypes.newsym do acc + getbasetype(alltypes, p)/for(acc)
  [ newsymbol( "createthreadY", moduleref(" builtin" ,parameter.resulttype.sym), paras, getbasetype(alltypes, resulttype.sym))]
 else if(name.sym)_1 ∈ "assert"then
 let t = getbasetype(alltypes, parameter.modname.newsym)
  [abortsymbol.t]
  else if (name.sym)_1 ∈ "load "  then
     [Idx.getbasetype(alltypes, parameter.modname.newsym)]
 else if(name.sym)_1 ∈ "setfld"then [ newsym]
 else if sym=symbol3("T builtin","bitcast",seqof.seqof.typeT,seqof.typeT)  then
  [ symbol("bitcast(ptr)","builtin","ptr")]
 else if fsig.sym = "toseqX:T(ptr)" ∨ fsig.sym = "bitcast(T)"
 ∨ fsig.sym = "bitcast(T blockseq)"then
 let t = getbasetype(alltypes, resulttype.newsym)
  [symbol3("builtin","toseq:" + print.t,typeptr,t) ]
 else
  assert sym=symbol3("T builtin","allocateseq:T",typeint,typeint,typeint,seqof.typeT) report"not expecting" + print.sym
      [replaceTsymbol(getbasetype(alltypes, resulttype.newsym),
        symbol("allocateseq:T(int,int,int)","builtin","T"))]
  
 
function blocksym(alltypes:typedict, type:mytype)symbol
let z = getbasetype(alltypes, type)
let kind =(typerep.z)_(-2)
 if kind ∈ "real"then symbol("blockit(real seq)","real taublockseq","real seq")
 else if kind ∈ "int byte bit boolean"then symbol("blockit(int seq)","int taublockseq","int seq")
 else if kind ∈ "ptr seq"then symbol("blockit(ptr seq)","ptr taublockseq","ptr seq")
 else
  assert kind ∈ "packed2 packed3 packed4 packed5 packed6"report"blocksym problem"
   symbol("blockit(" + kind + "seq)","tausupport", [ kind,"seq"_1])

function encodenocode(typ:mytype)seq.symbol
let gl = symbol("global:" + print.typ,"$global","int seq")
let setfld = symbol("setfld(int, int seq, int)","int builtin","int")
let encodenosym = newsymbol("encodingno", moduleref."tausupport", [ seqof.typeword ], typeint)
 if typ = typeref(moduleref."tausupport","typename" ) then [ Lit.0, gl, Lit.2, setfld, Define."xx",gl]+Fld(0,typeint) 
 else if typ = seqof.typeref(moduleref."?","char")then
  [ Lit.0, gl, Lit.1, setfld, Define."xx", gl]+Fld(0,typeint) 
 else
  ifthenelse([ gl]+Fld( 0,typeint)+[ Lit.0, EqOp], [ Lit.0, gl, Words.typerep.typ, encodenosym, setfld, Define."xx", gl ]+Fld(0,typeint), [ gl]+Fld(0,typeint) , typeint)

function definedeepcopy(alltypes:typedict, type:mytype, org:seq.word)seq.symbol
 if type=typeint /or type=typeword  /or isencoding.type  then [ Local.1]
 else if isseq.type   then
 let basetype = getbasetype(alltypes, type)
  if  basetype =typeint /or basetype=typereal /or basetype=typeboolean  then [ Local.1, blocksym(alltypes, type)]
  else
   let cat = newsymbol("+", type, [ type, parameter.type], type)
   let resulttype = basetype
   let elementtype = parameter.basetype
   let element = newsymbol("element", moduleref("$for", elementtype), empty:seq.mytype, elementtype)
   let acc = newsymbol("acc", moduleref("$for", typeptr), empty:seq.mytype, typeptr)
   let idx = newsymbol("idx", moduleref."$for", empty:seq.mytype, typeint)
    Emptyseq.elementtype
    + [ Local.1, acc, element, acc, element, deepcopysym(alltypes, parameter.type), cat, Littrue, acc, newsymbol("forexp", moduleref("builtin",typeint), [ resulttype, resulttype, resulttype, elementtype, typeptr, typeboolean, resulttype], resulttype)
    ]
    + blocksym(alltypes, type)
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