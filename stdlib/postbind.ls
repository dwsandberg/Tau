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
 let root = newsymbol("Wroot", mytype."W", empty:seq.mytype, typeint)
  postbindc(alltypes, dict,[root],map(theprg, root, roots),templates,emptyprogram)  

Function postbindc(alltypes:typedict, dict:set.symbol,
  toprocess:seq.symbol,  sourceX:program, tempX:program,resultX:program)program
  if isempty.toprocess then resultX else 
  for    working=empty:set.symbol,result=resultX,source=sourceX,calls=empty:set.symbol,s = toprocess  do 
   let w = working + s
    if cardinality.w = cardinality.working &or  isdefined.lookupcode(result,s) then  
         next( w,result,source,calls)
   else 
     let lr1 = lookupcode(source, s)
    \\ assert isdefined.lr1 report"postbind:expected to be defined:" + print.s \\
     let r= postbind3b(alltypes,dict,code.lr1,parameter.modname.s,print.s, source, tempX)
          next(w-s,if   s=newsymbol("Wroot", mytype."W",  empty:seq.mytype, typeint)  then result
        else map(result, s, code.r),sourceX.r,(calls &cup calls.r ) )
    end( postbindc(alltypes,dict,toseq.calls,source,tempX,result))

type resultpb is calls:set.symbol, code:seq.symbol, sourceX:program



function postbind3b(alltypes:typedict, dict:set.symbol, code:seq.symbol,modpara:mytype, org:seq.word, source:program, tempX:program
)resultpb
          let coretypes=false
 for  result=empty:seq.symbol ,calls=empty:set.symbol,sourceX=source, x = code do
      if isspecial.x then 
     let a=if isSequence.x then
        Sequence(parameter.getbasetype(alltypes,replaceT(modpara,resulttype.x)), nopara.x)
   else  if isblock.x then
         Block( getbasetype(coretypes,alltypes,replaceT(modpara,resulttype.x)), nopara.x)  
      else  x   
       next(result+a,calls,sourceX )  
    else 
    let isfref = isFref.x
    let sym = basesym.x
       if isconst.sym   ∨ last.module.sym ∈ "$global"then
         next(result+x,calls,sourceX)  
       else if module.sym = "builtin"  then
         next(result+x,calls+sym,sourceX)
       else if last.module.sym ∈ "$for"then
              next(result+replaceTsymbol(modpara, sym),calls,sourceX)  
      else
      let lr1 = lookupcode(sourceX, sym)
      let newsym = if isempty.typerep.modpara ∨ isdefined.lr1 then sym else replaceTsymbol(modpara, sym)
      let xx4 = if newsym = sym then lr1 else \\ check to see if template already has been processed \\ lookupcode(sourceX, newsym)
       if isdefined.xx4 then
       let p2 =if isfref then [Fref.target.xx4 ]  
               else if   "VERYSIMPLE"_1 ∈ getoption.code.xx4 then
            subseq(code.xx4, nopara.newsym + 1, length.code.xx4 - 2)
             else [  target.xx4]
          next( result + p2, calls + target.xx4, sourceX)
       else if last.module.sym = "builtin"_1 then
       if fsig.sym = "processresult(T process)"then
         let codeforbuiltin =  [ Local.1, Lit.2, Idx.getbasetype(alltypes, parameter.modname.newsym)]
          next(result + if isfref then Fref.newsym else newsym,calls + newsym, map(sourceX, newsym, codeforbuiltin))
    else if fsig.sym = "primitiveadd(int, T encodingpair)"then
       let addefunc = newsymbol("add", addabstract("encoding"_1, parameter.modname.newsym), [ addabstract("encodingstate"_1, parameter.modname.newsym), addabstract("encodingpair"_1, parameter.modname.newsym)], addabstract("encodingstate"_1, parameter.modname.newsym))
       let add2 = newsymbol("addencoding", mytype."builtin", [ typeint, mytype."ptr", typeint, typeint], typeint)
       let dc = deepcopysym(alltypes, addabstract("encodingpair"_1, parameter.modname.newsym))
     let codeforbuiltin =  [ Local.1, Local.2, Fref.addefunc, Fref.dc, add2, Words."NOINLINE STATE", Optionsym]
        next(result + if isfref then Fref.newsym else newsym,calls + newsym, map(sourceX, newsym, codeforbuiltin))
  else if  fsig.sym = "getinstance:encodingstate.T" then 
   let get = symbol("getinstance(int)","builtin","ptr")
  let codeforbuiltin =  encodenocode.parameter.modname.newsym + [ get, Words."NOINLINE STATE", Optionsym]
           next(result + if isfref then Fref.newsym else newsym,calls + newsym, map(sourceX, newsym, codeforbuiltin))
   else if fsig.sym = "packedindex(T seq, int)"then
 let z = getbasetype(alltypes,(paratypes.newsym)_1)
  let p2 = if maybepacked.z then packedindex2.z else [ IdxS.z]
   next(result + p2,    calls, sourceX )
 else let p2=codeforbuiltin(alltypes,   length.result > 0,   newsym, sym,modpara )
       next(result + p2,    calls, sourceX )
       else if subseq(fsig.sym, 1, 2) = "type:"then
       let p2 = definedeepcopy(alltypes, resulttype.newsym, org)
        next(result + if isfref then Fref.newsym else newsym,  calls + newsym, map(sourceX, newsym, p2) )
         else 
        let fx=handletemplate( dict,   newsym ,org,sourceX,tempX )
  let k=first.fx
  let newsource =if  length.fx=1 then sourceX else  map(sourceX, k,  fx << 1)
  next( result + if isfref then Fref.k else k,  calls + k, newsource)
  end (resultpb(calls, result, sourceX))




function buildconstructor(alltypes:typedict, addfld:seq.mytype, flds:seq.seq.mytype, flatflds:seq.mytype, fldno:int, j:int, subfld:int, result:seq.symbol)seq.symbol
 if fldno > length.flds then result + Record(addfld + flatflds)
 else
  let fldsubfields = flds_fldno
  let newflatflds = if j > length.flatflds then
  flatflds + for acc = empty:seq.mytype, @e = fldsubfields do acc + getbasetype(alltypes, @e)end(acc)
  else flatflds
  let newresult = result
  + if length.fldsubfields = 1 then [ Local.fldno]else [ Local.fldno, Lit.subfld, Idx.newflatflds_j]
   if subfld = length.fldsubfields - 1 then
   buildconstructor(alltypes, addfld, flds, newflatflds, fldno + 1, j + 1, 0, newresult)
   else buildconstructor(alltypes, addfld, flds, newflatflds, fldno, j + 1, subfld + 1, newresult)


 

function     handletemplate(dict:set.symbol , sym:symbol,org:seq.word,sourceX:program,tempX:program) seq.symbol
     let fx = lookupcode(tempX, sym)
        if isdefined.fx then  
           if isdefined.lookupcode(sourceX, sym)then [sym] else   [sym] +code.fx 
        else   
        let k = lookup(dict, name.sym, paratypes.sym)
    assert cardinality.k = 1 report"Cannot find template for" + name.sym + "("
   + for acc ="", @e = paratypes.sym do list(acc,",", print.@e)end(acc)
    + ")"
    + "while processing"
    + org
     assert not(sym = k_1)report"ERR12" + print.sym + print.k_1
     let dd = lookupcode(sourceX, k_1)
      if isdefined.dd then  [k_1]
      else
      \\ handles parameterized unbound cases like ?(int arc, int arc)graph.int \\ 
      handletemplate( dict,k_1,org,sourceX,tempX )

   

function buildcode(acc:int, w:word)int
 acc * 2 + if w = first."real"then 1 else 0

function getbasetype(coretypes :boolean,alltypes:typedict,t:mytype) mytype
let a=getbasetype(alltypes, t)
 if length.typerep.a > 2 ∧ coretypes then typeptr else a

function codeforbuiltin(alltypes:typedict, issequence:boolean,  newsym:symbol, sym:symbol,modpara:mytype) seq.symbol
         let coretypes=false
  if(fsig.sym)_1 ∈ "offsets"then
 \\ symbol(offset(<rettype> <types with unknownsize >, <knowoffset> +"builtin", <rettype>)\\
  let paratypes = paratypes.sym
         let offset = for acc = toint.(module.sym)_1, @e = subseq(paratypes, 2, length.paratypes)do acc + length.getsubflds(alltypes, replaceT(modpara, @e))end(acc)
   let  singlefld= 1 =length.getsubflds(alltypes, replaceT(modpara, resulttype.sym))
   if singlefld then [ Lit.offset, Idx.getbasetype(coretypes,alltypes, replaceT(modpara, resulttype.sym))]
   else [ Lit.offset, symbol("GEP(ptr seq, int)","internal","ptr")]
        else if(fsig.sym)_1 ∈ "build"then
 let c = for acc = empty:seq.seq.mytype, @e = paratypes.sym do acc + getsubflds(alltypes, replaceT(modpara, @e))end(acc)
   buildconstructor(alltypes, if issequence then \\ for seq index func \\ [ typeint]else empty:seq.mytype, c, empty:seq.mytype, 1, 1, 0, empty:seq.symbol)
 else if fsig.sym = "unpackedindex(T seq, int)"then
 let kind = seqeletype.getbasetype(alltypes, first.paratypes.newsym)
    [ Lit.1, PlusOp, Idx.kind]
 else if first.fsig.sym = first."createthreadX"then
 let paracode = buildargcode(alltypes, newsymbol("dummy", typeint, paratypes.newsym << 5, parameter.resulttype.newsym))
 let kindlist = for acc = empty:seq.mytype, @e = paratypes.sym << 5 do acc + getbasetype(alltypes, replaceT(modpara, @e))end(acc)
 [ Record([ typeint, typeint] + kindlist), symbol("toseqX:seq.int(ptr)","tausupport","int seq"), Lit.paracode, newsymbol("createthread", mytype."tausupport", [ typeint, typeint, typeint, mytype."int seq", typeint], typeptr)]
 else if(fsig.sym)_1 ∈ "callidx"then
  [Callidx.getbasetype(alltypes,(paratypes.newsym)_1)]
 else if fsig.sym = "packed(T seq)"then
    [blocksym(alltypes,(paratypes.newsym)_1)]
else  if(fsig.sym)_1 = "forexp"_1 then
 let paras = for acc = empty:seq.mytype, p = paratypes.newsym do acc + getbasetype(alltypes, p)end(acc)
   [ newsymbol("forexp", mytype."builtin", paras, last.paras) ]
 else  if(fsig.sym)_1 ∈ "assert"then
    let t=getbasetype(alltypes, parameter.modname.newsym)
   let kind= if abstracttype.t &in "seq" then "ptr" else typerep.t
   [symbol("assert:" + kind + "(word seq)","builtin", kind)]
  else if subseq(fsig.sym,1,2)  = "IDX:" then
 [Idx.getbasetype(alltypes, parameter.modname.newsym)]
  else if subseq(fsig.sym,1,2)  = "IDX(" then
    [Idx.seqeletype.getbasetype(alltypes, first.paratypes.newsym)]
  else if(fsig.sym)_1 ∈ "setfirst setfld"then
    [newsym]
  else if fsig.sym ="bitcast(T seq seq)"  then
     [symbol("bitcast(ptr)","builtin","ptr")]
 else if fsig.sym = "toseqX:T(ptr)" ∨ fsig.sym = "bitcast(T)"
 ∨ fsig.sym = "bitcast(T blockseq)"then
    let t=  getbasetype(alltypes, resulttype.newsym) 
     [symbol("toseq:" + print.t + "(ptr)","builtin", typerep.t)]
 else  assert  fsig.sym = "allocatespace:T(int)" report"not expecting" + print.sym
 [symbol(fsig.newsym,"builtin",returntype.newsym)]
 

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
 let encodenosym = newsymbol("encodingno", mytype."tausupport", [ mytype."word seq"], typeint)
  if typ = mytype."typename"then [ Lit.0, gl, Lit.2, setfld, Define."xx", gl, Lit.0, IdxInt]
  else if typ = mytype."char seq"then
  [ Lit.0, gl, Lit.1, setfld, Define."xx", gl, Lit.0, IdxInt]
  else
   [ gl, Lit.0, IdxInt, Lit.0, EqOp, Lit.3, Lit.2, Br, gl, Lit.0
   , IdxInt, Exit, Lit.0, gl, Words.typerep.typ, encodenosym, setfld, Define."xx", gl, Lit.0
   , IdxInt, Exit, Block(typeint, 3)]

function definedeepcopy(alltypes:typedict, type:mytype, org:seq.word)seq.symbol
 if abstracttype.type ∈ "encoding int word"then [ Local.1]
 else if abstracttype.type = "seq"_1 then
   let basetype=getbasetype(alltypes,  type)
     if abstracttype.basetype ∈ "int real boolean"then [ Local.1, blocksym(alltypes, type)]
   else
    let cat = newsymbol("+", type, [ type, parameter.type], type)
    let resulttype = basetype
    let elementtype =  parameter.basetype
    let element = newsymbol("element", addabstract("$for"_1, elementtype), empty:seq.mytype, elementtype)
    let acc = newsymbol("acc", addabstract("$for"_1, mytype."ptr"), empty:seq.mytype, mytype."ptr")
    let idx = newsymbol("idx", mytype."$for", empty:seq.mytype, typeint)
     Emptyseq.elementtype
   +      [ Local.1 
        , acc 
        , element
        , acc, element, deepcopysym(alltypes,parameter.type), cat
        , Littrue
        , acc
        ,  newsymbol("forexp", mytype."int builtin", 
         [ resulttype,resulttype,resulttype, elementtype, typeptr, mytype."boolean",resulttype], resulttype)
    ]
     + blocksym(alltypes, type)
 else
  let subflds= getsubflds(alltypes, type)
  let y = subfld(alltypes, subflds , 1, empty:seq.mytype, empty:seq.symbol)
   if length.subflds  = 1 then
   \\ only one element in record so type is not represent by actual record \\
    [ Local.1] + subseq(y, 4, length.y - 1)
   else y

function subfld(alltypes:typedict, flds:seq.mytype, fldno:int, fldkinds:seq.mytype, result:seq.symbol)seq.symbol
 if fldno > length.flds then result + [ Record.fldkinds]
 else
  let fldtype = flds_fldno
  let kind = getbasetype(alltypes, fldtype)
   subfld(alltypes, flds, fldno + 1, fldkinds + kind, result + [ Local.1, Lit(fldno - 1), Idx.kind, deepcopysym(alltypes, fldtype)])