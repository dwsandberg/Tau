module postbind

use standard

use symbol

use seq.myinternaltype

use seq.mytype

use seq.symbol

use set.symbol

use seq.typeinfo

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
    \\ if(fsig.s)_1 &in"indexseq"then postbind(alltypes, dict, w, toprocess, i + 1, result, sourceX, tempX)else \\
    let lr1 = lookupcode(sourceX, s)
     assert isdefined.lr1 report"postbind:expected to be defined:" + print.s
      if"BUILTIN"_1 ∈ getoption.code.lr1 then
      postbind(alltypes, dict, w, toprocess, i + 1, map(result, s, code.lr1), sourceX, tempX)
      else
       let modname = mytype.module.s
       let r = postbind3(alltypes, dict, code.lr1, 1, empty:seq.symbol, parameter.modname, print.s, empty:set.symbol, sourceX, tempX)
        postbind(alltypes
        , dict
        , w
        , toseq(calls.r - w) + subseq(toprocess, i + 1, length.toprocess)
        , 1
        , if length.toprocess = 1 ∧ toprocess_1 = newsymbol("Wroot", mytype."W", empty:seq.mytype, typeint)then
        result
        else map(result, s, code.r)
        , sourceX.r
        , tempX)

type resultpb is record calls:set.symbol, code:seq.symbol, sourceX:program

function postbind3(alltypes:typedict, dict:set.symbol, code:seq.symbol, i:int, result:seq.symbol, modpara:mytype, org:seq.word, calls:set.symbol, sourceX:program, tempX:program)resultpb
 if i > length.code then resultpb(calls, result, sourceX)
 else
  let x = code_i
  let isfref = isFref.x
  let sym = basesym.x
   if isblock.sym then
   let a = Block(mytype.[ kind(alltypes, modpara, resulttype.sym)], nopara.sym)
     postbind3(alltypes, dict, code, i + 1, result + if isfref then Fref.a else a, modpara, org, calls, sourceX, tempX)
   else if isconst.sym ∨ isspecial.sym ∨ module.sym = "builtin"
   ∨ last.module.sym ∈ "$global "then
   \\ assert module.sym &ne"builtin"&or fsig.sym &in ["addencoding(int, int seq, int, int)","aborted(T process)","getinstance(int)","option(int, word seq)"]report"builtinX"+ print.sym \\
    postbind3(alltypes, dict, code, i + 1, result + code_i, modpara, org, calls, sourceX, tempX)
   else if  last.module.sym ∈ "$for"then
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
     else if"ABSTRACTBUILTIN"_1 ∈ options ∨ last.module.sym = "builtin"_1 then
     \\ assert("ABSTRACTBUILTIN"_1 ∈ options)=(last.module.sym ="builtin"_1)&or first.module.sym ="T"_1 &or(fsig.sym)_1 &in"  kindrecord offsets build assert createthreadX"report"BBBBBB"+ print.sym \\
      codeforbuiltin(alltypes, dict, code, i, result, isfref, newsym, sym, org, modpara, calls, sourceX, tempX)
     else if subseq(fsig.sym, 1, 2) = "type:"then
     let p2 = definedeepcopy(alltypes, resulttype.newsym, org)
       \\ assert false report"XXX"+ print.newsym \\
       postbind3(alltypes, dict, code, i + 1, result + if isfref then Fref.newsym else newsym, modpara, org, calls + newsym, map(sourceX, newsym, p2), tempX)
     else handletemplates(alltypes, dict, code, i, result, isfref, newsym, modpara, org, calls, sourceX, tempX)

codeforbuiltin(alltypes, dict, code, i, result, calls, sourceX, tempX, newsym, sym, org, modpara, isfref)

function kind(alltypes:typedict, with:mytype, a:mytype)word kind.gettypeinfo(alltypes, replaceT(with, a))

function kind(alltypes:typedict, a:mytype)word kind.gettypeinfo(alltypes, a)

function subflds(alltypes:typedict, with:mytype, a:mytype)seq.mytype subflds.gettypeinfo(alltypes, replaceT(with, a))

function Size(alltypes:typedict, with:mytype, a:mytype)int size.gettypeinfo(alltypes, replaceT(with, a))

function buildconstructor(alltypes:typedict, addfld:seq.word, flds:seq.seq.mytype, flatflds:seq.word, fldno:int, j:int, subfld:int, result:seq.symbol)seq.symbol
 if fldno > length.flds then result + Record(addfld + flatflds)
 else
  let fldsubfields = flds_fldno
  let newflatflds = if j > length.flatflds then
  flatflds + ((for(@e ∈ fldsubfields, acc ="")acc + kind(alltypes, @e)))
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
    postbind3(alltypes, dict, code, i + 1, result + if isfref then Fref.sym else sym, modpara, org, calls + sym, newsource, tempX)
  else
   let k = lookup(dict, name.sym, paratypes.sym)
    assert cardinality.k = 1 report"Cannot find template for" + name.sym + "("
    + (for(@e ∈ paratypes.sym, acc ="")list(acc,",", print.@e))
    + ")"
    + "while processing"
    + org
     assert not(sym = k_1)report"ERR12" + print.sym + print.k_1
     let dd = lookupcode(sourceX, k_1)
      if isdefined.dd then
      postbind3(alltypes, dict, code, i + 1, result + if isfref then Fref.k_1 else k_1, modpara, org, calls + k_1, sourceX, tempX)
      else
       \\ handles parameterized unbound cases like ?(int arc, int arc)graph.int \\
       handletemplates(alltypes, dict, code, i, result, isfref, k_1, modpara, org, calls, sourceX, tempX)

function buildcode(acc:int, w:word)int acc * 2 + if w = first."real"then 1 else 0

function codeforbuiltin(alltypes:typedict, dict:set.symbol, code:seq.symbol, i:int, result:seq.symbol, isfref:boolean, newsym:symbol, sym:symbol, org:seq.word, modpara:mytype
, calls:set.symbol, sourceX:program, tempX:program)resultpb
 if(fsig.sym)_1 ∈ "offsets"then
 \\ symbol(offset(<rettype> <types with unknownsize >, <knowoffset> +"builtin", <rettype>)\\
  let paratypes = paratypes.sym
   \\ assert not.isempty.typerep.last.paratypes report"XXX"+ print.sym \\
   let offset =((for(@e ∈ subseq(paratypes, 2, length.paratypes), acc = toint.(module.sym)_1)acc + Size(alltypes, modpara, @e)))
   let resultinfo = gettypeinfo(alltypes, replaceT(modpara, resulttype.sym))
   let p2 = if size.resultinfo = 1 then [ Lit.offset, Idx.kind.resultinfo]
   else [ Lit.offset, symbol("GEP(ptr seq, int)","internal","ptr")]
    postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
 else if(fsig.sym)_1 ∈ "build"then
 let c =((for(@e ∈ paratypes.sym, acc = empty:seq.seq.mytype)acc + subflds(alltypes, modpara, @e)))
  let p2 = buildconstructor(alltypes, if i = 2 then \\ for seq index func \\"int"else"", c,"", 1, 1, 0, empty:seq.symbol)
   postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
 else if(fsig.sym)_1 ∈ "kindrecord"then
 let p2 = Record.((for(@e ∈ paratypes.sym, acc ="")acc + kind(alltypes, modpara, @e)))
   postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
 else if first.fsig.sym = first."createthreadX"then
 let kindlist =((for(@e ∈ paratypes.sym << 5, acc ="")acc + kind(alltypes, modpara, @e)))
  let paracode =(for(@e ∈ kindlist + kind(alltypes, modpara, parameter.resulttype.sym), acc = 1)buildcode(acc, @e))
  let p2 = [ Record("int int" + kindlist), Lit.paracode, newsymbol("createthread", mytype."tausupport", [ typeint, typeint, typeint, mytype."int seq", typeint], typeptr)]
   postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
 else if fsig.sym = "indexseq(T seq, int)"then
 let elementtype = parameter.modname.newsym
  let p2 = if elementtype = mytype."byte"then [ symbol("extractbyte(int seq, int)","internal","int")]
  else if elementtype = mytype."bit"then [ symbol("extractbit(int seq, int)","internal","int")]
  else
   let info = gettypeinfo(alltypes, elementtype)
   let size = size.gettypeinfo(alltypes, elementtype)
    [ Lit.size, MultOp, Lit.2, PlusOp, symbol("GEP(ptr seq, int)","internal","ptr")]
   postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
 else if(fsig.sym)_1 = "apply5"_1 then
 let paras = paratypes.newsym
  let eletype = paras_3
  let resulttype = mytype.[ kind.gettypeinfo(alltypes, paras_4)]
  let info = gettypeinfo(alltypes, eletype)
  let neweletype = mytype
  .[ if size.info > 1 then toword.size.info
  else if eletype ∈ [ mytype."byte", mytype."bit"]then abstracttype.eletype else kind.info]
  let p2 = newsymbol("apply5", mytype."builtin", [ resulttype, abstracttype("seq"_1, neweletype), neweletype, resulttype, typeint, resulttype, mytype."boolean"], resulttype)
   postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
 else if(fsig.sym)_1 ∈ "assert"then
  let kind=[kind.gettypeinfo(alltypes, parameter.modname.newsym)]
   let p2 = symbol("assert:"+kind+"(word seq)","builtin", kind)
   postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
 else if(fsig.sym)_1 ∈ "callidx"then
 let sym2 = replaceTsymbol(mytype.[ kind.gettypeinfo(alltypes, parameter.modname.newsym)], sym)
  let p2 = symbol(fsig.sym2,"$internal", returntype.sym2)
   postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
 else if fsig.sym ∈ ["IDX2(T seq, int)"]then
 let kind = kind.gettypeinfo(alltypes, parameter.modname.newsym)
   postbind3(alltypes, dict, code, i + 1, result + replaceTsymbol(mytype.[ kind], sym), modpara, org, calls, sourceX, tempX)
 else if fsig.sym = "IDX(T seq, int)"then
 let kind = kind.gettypeinfo(alltypes, parameter.modname.newsym)
   postbind3(alltypes, dict, code, i + 1, result + Idx.kind, modpara, org, calls, sourceX, tempX)
 else if(fsig.sym)_1 ∈ "assert callidx  callidx2 GEP extractbyte extractbit"
 ∨ fsig.sym ∈ ["setfld(int, T seq, T)","setfirst(T seq, int, int)"]then
 let kind = kind.gettypeinfo(alltypes, parameter.modname.newsym)
  let p2 = symbol(fsig.sym, [ kind] + "builtin", returntype.newsym)
   postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
 else if fsig.sym ∈ ["bitcast(T blockseq)","bitcast(T seq seq)","bitcast(T)"]then
 postbind3(alltypes, dict, code, i + 1, result, modpara, org, calls, sourceX, tempX)
 else if fsig.sym = "allocatespace:T(int)"then
 let p2 = symbol("allocatespace(int)","tausupport","int seq")
   postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
 else if fsig.sym = "sizeoftype:T"then
 let size = if parameter.modname.newsym = mytype."byte"then-8
  else if parameter.modname.newsym = mytype."bit"then-1 else size.gettypeinfo(alltypes, parameter.modname.newsym)
  let p2 = Lit.size
   postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
 else
  let codeforbuiltin = if fsig.sym = "processresult(T process)"then
  [ Local.1, Lit.2, Idx.kind.gettypeinfo(alltypes, parameter.modname.newsym)]
  else if fsig.sym = "packed(T seq)"then
  [ Local.1] + blocksym.gettypeinfo(alltypes, parameter.modname.newsym)
  else if fsig.sym = "primitiveadd(int, T encodingpair)"then
  let addefunc = newsymbol("add", typeencoding + parameter.modname.newsym, [ typeencodingstate + parameter.modname.newsym, typeencodingpair + parameter.modname.newsym], typeencodingstate + parameter.modname.newsym)
   let add2 = newsymbol("addencoding", mytype."builtin", [ typeint, mytype."int seq", typeint, typeint], typeint)
   let dc = deepcopysym(alltypes, typeencodingpair + parameter.modname.newsym)
    [ Local.1, Local.2, Fref.addefunc, Fref.dc, add2, Words."NOINLINE STATE", Optionsym]
  else
   assert fsig.sym = "getinstance:encodingstate.T"report"not expecting" + print.sym
   let get = symbol("getinstance(int)","builtin","ptr")
    encodenocode.parameter.modname.newsym + [ get, Words."NOINLINE STATE", Optionsym]
   postbind3(alltypes, dict, code, i + 1, result + if isfref then Fref.newsym else newsym, modpara, org, calls + newsym, map(sourceX, newsym, codeforbuiltin), tempX)

function blocksym(info:typeinfo)seq.symbol
 let ds = size.info
  if kind.info = "real"_1 then
  [ symbol("blockit(real seq)","tausupport","real seq")]
  else if ds = 1   then [ symbol("blockit(int seq)","tausupport","int seq")]
  else  if ds < 6 then
      let  xx=[ merge("packed"+toword.ds)]
          [symbol("blockit("+xx+"seq)","tausupport",xx+"seq")]
      else [symbol("blockit( ptr seq)","tausupport", "ptr seq")]
      
    

function encodenocode(typ:mytype)seq.symbol
 let gl = symbol("global:" + print.typ,"$global","int seq")
 let setfld = symbol("setfld(int, int seq, int)","$internal","int")
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
 let ds = size.gettypeinfo(alltypes, type)
  let info = gettypeinfo(alltypes, parameter.type)
  let kind = kind.info
  let typepara = if kind ∈ "int real"then mytype.[ kind]else parameter.type
  let seqtype = typeseq + typepara
  let dc = deepcopysym(alltypes, typepara)
  let cat = newsymbol("+", seqtype, [ seqtype, typepara], seqtype)
  let resulttype = mytype."ptr"
  let elementtype = mytype.[ kind]
  let element= newsymbol("element", abstracttype("$for"_1, elementtype), empty:seq.mytype, elementtype) 
  let acc=     newsymbol("acc", abstracttype("$for"_1, mytype."ptr"), empty:seq.mytype, mytype."ptr")
  let idx=     newsymbol("idx", mytype."$for", empty:seq.mytype, typeint)
   Emptyseq +[ Local.1,element,acc,idx,acc,element,dc,cat,Litfalse,
     newsymbol("apply5", mytype."builtin", [ resulttype, abstracttype("seq"_1, elementtype), elementtype, resulttype, typeint, resulttype, mytype."boolean"], resulttype)
]
   + blocksym.info
 else
  let typedesc = gettypeinfo(alltypes, type)
  let y = subfld(alltypes, subflds.typedesc, 1,"", empty:seq.symbol)
   if size.typedesc = 1 then
   \\ only one element in record so type is not represent by actual record \\
    [ Local.1] + subseq(y, 4, length.y - 1)
   else
    assert size.typedesc ≠ 1 report"Err99a" + print.type
     y
 

function subfld(alltypes:typedict, flds:seq.mytype, fldno:int, fldkinds:seq.word, result:seq.symbol)seq.symbol
 if fldno > length.flds then result + [ Record.fldkinds]
 else
  let fldtype = flds_fldno
  let kind = kind.gettypeinfo(alltypes, fldtype)
   subfld(alltypes, flds, fldno + 1, fldkinds + kind, result + [ Local.1, Lit(fldno - 1), Idx.kind, deepcopysym(alltypes, fldtype)])