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

/function print3(s:symbol)seq.word if(zcode.s)_1 = s then print.s else print.s +"->"+ print.(zcode.s)_1 + if length.zcode.s = 1 then"NO CODE"else""

Function postbind(alltypes:typedict, dict:set.symbol, roots:seq.symbol, theprg:program, templates:program)program
 let root = newsymbol("Wroot", mytype."W", empty:seq.mytype, typeint)
  postbind(alltypes, dict, empty:set.symbol, [ root], 1, emptyprogram, map(theprg, root, roots), templates)

function postbind(alltypes:typedict, dict:set.symbol, working:set.symbol, toprocess:seq.symbol, i:int, result:program, sourceX:program, tempX:program)program
 if i > length.toprocess then result
 else
  let s = toprocess_i
  let w = working + s
   if cardinality.w = cardinality.working then postbind(alltypes, dict, w, toprocess, i + 1, result, sourceX, tempX)
   else
    let lr1 = lookupcode(sourceX, s)
     assert isdefined.lr1 report"postbind:expected to be defined:" + print.s
      if"BUILTIN"_1 ∈ getoption.code.lr1 then
      postbind(alltypes, dict, w, toprocess, i + 1, map(result, s, code.lr1), sourceX, tempX)
      else
       let modname = mytype.module.s
       let r = postbind3(alltypes, dict, code.lr1, 1, empty:seq.symbol, parameter.modname, print.s, empty:set.symbol, sourceX, tempX)
        postbind(alltypes, dict, w, toseq(calls.r - w) + subseq(toprocess, i + 1, length.toprocess), 1, if length.toprocess = 1 ∧ toprocess_1 = newsymbol("Wroot", mytype."W", empty:seq.mytype, typeint)then
        result
        else map(result, s, code.r), sourceX.r, tempX)

type resultpb is calls:set.symbol, code:seq.symbol, sourceX:program

function postbind3(alltypes:typedict, dict:set.symbol, code:seq.symbol, i:int, result:seq.symbol, modpara:mytype, org:seq.word, calls:set.symbol, sourceX:program, tempX:program
)resultpb
 if i > length.code then resultpb(calls, result, sourceX)
 else
         let coretypes=false
  let x = code_i
    if isspecial.x then 
   if isSequence.x then
    let a = Sequence(parameter.getbasetype(alltypes,replaceT(modpara,resulttype.x)), nopara.x)
     postbind3(alltypes, dict, code, i + 1, result + a, modpara, org, calls, sourceX, tempX)
   else  if isblock.x then
      let a = Block( getbasetype(coretypes,alltypes,replaceT(modpara,resulttype.x)), nopara.x)  
     postbind3(alltypes, dict, code, i + 1, result + a, modpara, org, calls, sourceX, tempX)
   else       postbind3(alltypes, dict, code, i + 1, result + x, modpara, org, calls, sourceX, tempX)
   else 
    let isfref = isFref.x
    let sym = basesym.x
       if isconst.sym ∨ module.sym = "builtin"  ∨ last.module.sym ∈ "$global"then
      postbind3(alltypes, dict, code, i + 1, result + code_i, modpara, org, calls, sourceX, tempX)
     else if last.module.sym ∈ "$for"then
     postbind3(alltypes, dict, code, i + 1, result + replaceTsymbol(modpara, sym), modpara, org, calls, sourceX, tempX)
     else
      let lr1 = lookupcode(sourceX, sym)
      let newsym = if isempty.typerep.modpara ∨ isdefined.lr1 then sym else replaceTsymbol(modpara, sym)
      let xx4 = if newsym = sym then lr1 else \\ check to see if template already has been processed \\ lookupcode(sourceX, newsym)
      let options = getoption.code.xx4
       if isdefined.xx4 then
       if not.isfref ∧ "VERYSIMPLE"_1 ∈ options then
        let p2 = subseq(code.xx4, nopara.newsym + 1, length.code.xx4 - 2)
          postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls + target.xx4, sourceX, tempX)
        else
         let p2 = if isfref then Fref.target.xx4 else target.xx4
          postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls + target.xx4, sourceX, tempX)
       else if last.module.sym = "builtin"_1 then
      if(fsig.sym)_1 ∈ "offsets"then
 \\ symbol(offset(<rettype> <types with unknownsize >, <knowoffset> +"builtin", <rettype>)\\
  let paratypes = paratypes.sym
         let offset = for acc = toint.(module.sym)_1, @e = subseq(paratypes, 2, length.paratypes)do acc + length.getsubflds(alltypes, replaceT(modpara, @e))end(acc)
   let  singlefld= 1 =length.getsubflds(alltypes, replaceT(modpara, resulttype.sym))
   let p2 = if singlefld then [ Lit.offset, Idx.getbasetype(coretypes,alltypes, replaceT(modpara, resulttype.sym))]
   else [ Lit.offset, symbol("GEP(ptr seq, int)","internal","ptr")]
    postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
        else codeforbuiltin(alltypes, dict, code, i, result, isfref, newsym, sym, org, modpara, calls, sourceX, tempX)
       else if subseq(fsig.sym, 1, 2) = "type:"then
       let p2 = definedeepcopy(alltypes, resulttype.newsym, org)
         \\ assert false report"XXX"+ print.newsym \\
        postbind3(alltypes, dict, code, i + 1, result + if isfref then Fref.newsym else newsym, modpara, org, calls + newsym, map(sourceX, newsym, p2), tempX
        )
       else handletemplates(alltypes, dict, code, i, result, isfref, newsym, modpara, org, calls, sourceX, tempX)

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

function handletemplates(alltypes:typedict, dict:set.symbol, code:seq.symbol, i:int, result:seq.symbol, isfref:boolean, sym:symbol, modpara:mytype, org:seq.word, calls:set.symbol
, sourceX:program, tempX:program)resultpb
 let fx = lookupcode(tempX, sym)
  if isdefined.fx then
  let newsource = if isdefined.lookupcode(sourceX, sym)then sourceX else map(sourceX, sym, code.fx)
  postbind3(alltypes, dict, code, i + 1, result + if isfref then Fref.sym else sym, modpara, org, calls + sym, newsource, tempX
  )
  else
   let k = lookup(dict, name.sym, paratypes.sym)
    assert cardinality.k = 1 report"Cannot find template for" + name.sym + "("
   + for acc ="", @e = paratypes.sym do list(acc,",", print.@e)end(acc)
    + ")"
    + "while processing"
    + org
     assert not(sym = k_1)report"ERR12" + print.sym + print.k_1
     let dd = lookupcode(sourceX, k_1)
      if isdefined.dd then
     postbind3(alltypes, dict, code, i + 1, result + if isfref then Fref.k_1 else k_1, modpara, org, calls + k_1, sourceX, tempX
      )
      else
       \\ handles parameterized unbound cases like ?(int arc, int arc)graph.int \\
       handletemplates(alltypes, dict, code, i, result, isfref, k_1, modpara, org, calls, sourceX, tempX)

function buildcode(acc:int, w:word)int
 acc * 2 + if w = first."real"then 1 else 0

function getbasetype(coretypes :boolean,alltypes:typedict,t:mytype) mytype
let a=getbasetype(alltypes, t)
 if length.typerep.a > 2 ∧ coretypes then typeptr else a

function codeforbuiltin(alltypes:typedict, dict:set.symbol, code:seq.symbol, i:int, result:seq.symbol, isfref:boolean, newsym:symbol, sym:symbol, org:seq.word, modpara:mytype
, calls:set.symbol, sourceX:program, tempX:program)resultpb
 if(fsig.sym)_1 ∈ "build"then
 let c = for acc = empty:seq.seq.mytype, @e = paratypes.sym do acc + getsubflds(alltypes, replaceT(modpara, @e))end(acc)
  let p2 = buildconstructor(alltypes, if i = 2 then \\ for seq index func \\ [ typeint]else empty:seq.mytype, c, empty:seq.mytype, 1, 1, 0, empty:seq.symbol)
   postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
 else if first.fsig.sym = first."createthreadX"then
 let paracode = buildargcode(alltypes, newsymbol("dummy", typeint, paratypes.newsym << 5, parameter.resulttype.newsym))
 let kindlist = for acc = empty:seq.mytype, @e = paratypes.sym << 5 do acc + getbasetype(alltypes, replaceT(modpara, @e))end(acc)
 let p2 = [ Record([ typeint, typeint] + kindlist), symbol("toseqX:seq.int(ptr)","tausupport","int seq"), Lit.paracode, newsymbol("createthread", mytype."tausupport", [ typeint, typeint, typeint, mytype."int seq", typeint], typeptr)]
   postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
 else if(fsig.sym)_1 ∈ "callidx"then
 postbind3(alltypes, dict, code, i + 1, result + Callidx.getbasetype(alltypes,(paratypes.newsym)_1), modpara, org, calls, sourceX, tempX)
 else if fsig.sym = "unpackedindex(T seq, int)"then
 let kind = seqeletype.getbasetype(alltypes, first.paratypes.newsym)
   postbind3(alltypes, dict, code, i + 1, result + [ Lit.1, PlusOp, Idx.kind], modpara, org, calls, sourceX, tempX)
 else if fsig.sym = "packedindex(T seq, int)"then
 let z = getbasetype(alltypes,(paratypes.newsym)_1)
  let p2 = if maybepacked.z then packedindex2.z else [ IdxS.z]
   postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
 else if fsig.sym = "packed(T seq)"then
 let p2 = blocksym(alltypes,(paratypes.newsym)_1)
   postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
else if(fsig.sym)_1 = "forexp"_1 then
 let paras = for acc = empty:seq.mytype, p = paratypes.newsym do acc + getbasetype(alltypes, p)end(acc)
  postbind3(alltypes, dict, code, i + 1, result + newsymbol("forexp", mytype."builtin", paras, last.paras), modpara, org, calls, sourceX, tempX
  )
 else if(fsig.sym)_1 ∈ "assert"then
    let t=getbasetype(alltypes, parameter.modname.newsym)
   let kind= if abstracttype.t &in "seq" then "ptr" else typerep.t
  let p2 = symbol("assert:" + kind + "(word seq)","builtin", kind)
   postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
 else if subseq(fsig.sym,1,2)  = "IDX:" then
 let p2 = Idx.getbasetype(alltypes, parameter.modname.newsym)
   postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
 else if subseq(fsig.sym,1,2)  = "IDX(" then
  let p2 = Idx.seqeletype.getbasetype(alltypes, first.paratypes.newsym)
   postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
 else if(fsig.sym)_1 ∈ "setfirst setfld"then
 postbind3(alltypes, dict, code, i + 1, result + newsym, modpara, org, calls, sourceX, tempX)
  else if fsig.sym ="bitcast(T seq seq)"  then
 postbind3(alltypes, dict, code + symbol("bitcast(ptr)","builtin","ptr"), i + 1, result, modpara, org, calls, sourceX, tempX
  )
 else if fsig.sym = "toseqX:T(ptr)" ∨ fsig.sym = "bitcast(T)"
 ∨ fsig.sym = "bitcast(T blockseq)"then
    let t=  getbasetype(alltypes, resulttype.newsym) 
  postbind3(alltypes, dict, code + symbol("toseq:" + print.t + "(ptr)","builtin", typerep.t), i + 1, result, modpara, org, calls, sourceX, tempX
  )
 else  if fsig.sym = "allocatespace:T(int)"then
 let p2 = symbol(fsig.newsym,"builtin",returntype.newsym)
   postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
 else 
  let codeforbuiltin = if fsig.sym = "processresult(T process)"then
  [ Local.1, Lit.2, Idx.getbasetype(alltypes, parameter.modname.newsym)]
  else if fsig.sym = "primitiveadd(int, T encodingpair)"then
  let addefunc = newsymbol("add", addabstract("encoding"_1, parameter.modname.newsym), [ addabstract("encodingstate"_1, parameter.modname.newsym), addabstract("encodingpair"_1, parameter.modname.newsym)], addabstract("encodingstate"_1, parameter.modname.newsym))
   let add2 = newsymbol("addencoding", mytype."builtin", [ typeint, mytype."ptr", typeint, typeint], typeint)
   let dc = deepcopysym(alltypes, addabstract("encodingpair"_1, parameter.modname.newsym))
    [ Local.1, Local.2, Fref.addefunc, Fref.dc, add2, Words."NOINLINE STATE", Optionsym]
  else
   assert fsig.sym = "getinstance:encodingstate.T"report"not expecting" + print.sym
   let get = symbol("getinstance(int)","builtin","ptr")
    encodenocode.parameter.modname.newsym + [ get, Words."NOINLINE STATE", Optionsym]
   postbind3(alltypes, dict, code, i + 1, result + if isfref then Fref.newsym else newsym, modpara, org, calls + newsym, map(sourceX, newsym, codeforbuiltin), tempX
   )

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