module postbind

use seq.myinternaltype

use seq.seq.mytype

use seq.mytype

use stdlib

use seq.symbol

use set.symbol

use symbol

use seq.typeinfo

/function print3(s:symbol)seq.word if(zcode.s)_1 = s then print.s else print.s +"->"+ print.(zcode.s)_1 + if length.zcode.s = 1 then"NO CODE"else""

Function postbind(alltypes:typedict, dict:set.symbol, roots:seq.symbol, theprg:program, templates:program)program
 let root = newsymbol("Wroot", mytype."W", empty:seq.mytype, typeint)
  postbind(alltypes, dict, empty:set.symbol, [ root], 1, emptyprogram, map(theprg, root, roots), templates)

function postbind(alltypes:typedict, dict:set.symbol, working:set.symbol, toprocess:seq.symbol, i:int, result:program, sourceX:program, tempX:program)program
 if i > length.toprocess then result
 else
  let s = toprocess_i
  let w = working + toprocess_i
   if cardinality.w = cardinality.working then postbind(alltypes, dict, w, toprocess, i + 1, result, sourceX, tempX)
   else
    let lr1 = lookupcode(sourceX, s)
     assert isdefined.lr1 report"postbind:expected to be defined:" + print.s
     let modname = mytype.module.s
      if // isbuiltin // modname = mytype."builtin"then postbind(alltypes, dict, w, toprocess, i + 1, result, sourceX, tempX)
      else
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
   else if isnocall.sym then postbind3(alltypes, dict, code, i + 1, result + code_i, modpara, org, calls, sourceX, tempX)
   else
    let lr1 = lookupcode(sourceX, sym)
    let newsym = if isdefined.lr1 then sym else replaceTsymbol(modpara, sym)
    let xx4 = if newsym = sym then lr1 else // check to see if template already has been processed // lookupcode(sourceX, newsym)
     if isdefined.xx4 then
     if not.isfref ∧ "VERYSIMPLE"_1 in options.code.xx4 then
      let p2 = subseq(code.xx4, nopara.newsym + 1, length.code.xx4 - 2)
        postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
      else
       let p2 = if isfref then Fref.target.xx4 else target.xx4
        postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls + target.xx4, sourceX, tempX)
     else if abstracttype.modname.sym in "builtin"then
     if(fsig.sym)_1 in "offsets"then
      // symbol(offset(<rettype> <types with unknownsize >, <knowoffset> +"builtin", <rettype>)//
       let paratypes = paratypes.sym
       let offset = subseq(paratypes, 2, length.paratypes) @@ +(toint.(module.sym)_1, Size(alltypes, modpara, @e))
       let resultinfo = gettypeinfo(alltypes, replaceT(modpara, resulttype.sym))
       let p2 = if size.resultinfo = 1 then [ Lit.offset, Idx.kind.resultinfo]
       else
        [ Lit.offset, Lit.size.resultinfo, symbol("cast(T seq, int, int)","builtin","ptr")]
        postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
      else if(fsig.sym)_1 in "build"then
      let c = paratypes.sym @@ +(empty:seq.seq.mytype, subflds(alltypes, modpara, @e))
       let p2 = buildconstructor(alltypes, if i = 2 then // for seq index func //"int"else"", c,"", 1, 1, 0, empty:seq.symbol)
        postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
      else if(fsig.sym)_1 in "kindrecord"then
      let p2 = Record(paratypes.sym @@ +("", kind(alltypes, modpara, @e)))
        postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
      else if fsig.sym="IDX2(T seq, int)" then
      let info= gettypeinfo(alltypes, parameter.modname.newsym)
      let p2=if size.info > 1 then
         let multop=symbol("*(int,int)","builtin","int")
           [  Lit.-1,PlusOp, Lit.size.info, multop,Lit.2,PlusOp,    Lit.size.info,symbol("cast(T seq, int, int)","builtin","ptr")]
         else [symbol("IDX(T seq, int)", [ kind.info] + "builtin",  returntype.newsym)]
          postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
      else if(fsig.sym)_1 in "  apply3  " then
            let kind = kind.gettypeinfo(alltypes, parameter.modname.newsym)
          let k = findindex(","_1, fsig.newsym)
        let info=gettypeinfo(alltypes, mytype.subseq(fsig.newsym, 3, k - 2))
        let a = kind.info
        let newfsig ="apply3(" + a + "seq" + subseq(fsig.newsym, k, length.fsig.newsym)
          let p2 =   symbol(newfsig, [ kind] + "builtin", returntype.newsym)
            postbind3(alltypes, dict, code, i + 1, (result  >> 1 )+Lit.size.info+ p2, modpara, org, calls, sourceX, tempX)    
        else if(fsig.sym)_1 in "assert callidx  @e @i @acc   IDX" 
          &or fsig.sym = "setfld(int, T seq, T)" then
       let kind = kind.gettypeinfo(alltypes, parameter.modname.newsym)
       let p2 =  symbol(fsig.sym, [ kind] + "builtin",  returntype.newsym)
          postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
      else if fsig.sym in ["bitcast(T blockseq)", "bitcast(T  seq seq)" ,"bitcast(T)" ]then
          postbind3(alltypes, dict, code, i + 1, result , modpara, org, calls, sourceX, tempX)   
      else 
       let codeforbuiltin = codeforbuiltin(alltypes, newsym, sym, org)
        postbind3(alltypes, dict, code, i + 1, result + if isfref then Fref.newsym else newsym, modpara, org, calls + newsym, map(sourceX, newsym, codeforbuiltin), tempX)
     else if subseq(fsig.sym, 1, 2) = "type:"then
     let p2 = definedeepcopy(alltypes, resulttype.newsym, org)
       // assert false report"XXX"+ print.newsym //
       postbind3(alltypes, dict, code, i + 1, result + if isfref then Fref.newsym else newsym, modpara, org, calls + newsym, map(sourceX, newsym, p2), tempX)
     else handletemplates(alltypes, dict, code, i, result, isfref, newsym, modpara, org, calls, sourceX, tempX)

function kind(alltypes:typedict, with:mytype, a:mytype)word kind.gettypeinfo(alltypes, replaceT(with, a))

function kind(alltypes:typedict, a:mytype)word kind.gettypeinfo(alltypes, a)

function subflds(alltypes:typedict, with:mytype, a:mytype)seq.mytype subflds.gettypeinfo(alltypes, replaceT(with, a))

function Size(alltypes:typedict, with:mytype, a:mytype)int size.gettypeinfo(alltypes, replaceT(with, a))

function buildconstructor(alltypes:typedict, addfld:seq.word, flds:seq.seq.mytype, flatflds:seq.word, fldno:int, j:int, subfld:int, result:seq.symbol)seq.symbol
 if fldno > length.flds then result + Record(addfld + flatflds)
 else
  let fldsubfields = flds_fldno
  let newflatflds = if j > length.flatflds then flatflds + fldsubfields @@ +("", kind(alltypes, @e))else flatflds
  let newresult = result
  + if length.fldsubfields = 1 then [ Local.fldno]else [ Local.fldno, Lit.subfld, Idx.newflatflds_j]
   if subfld = length.fldsubfields - 1 then
   buildconstructor(alltypes, addfld, flds, newflatflds, fldno + 1, j + 1, 0, newresult)
   else buildconstructor(alltypes, addfld, flds, newflatflds, fldno, j + 1, subfld + 1, newresult)

function handletemplates(alltypes:typedict, dict:set.symbol, code:seq.symbol, i:int, result:seq.symbol, isfref:boolean, oldsym:symbol, modpara:mytype, org:seq.word, calls:set.symbol
, sourceX:program, tempX:program)resultpb
  let fx = lookupcode(tempX, oldsym)
   if isdefined.fx then
   let newsource = if isdefined.lookupcode(sourceX, oldsym)then sourceX else map(sourceX, oldsym, code.fx)
     postbind3(alltypes, dict, code, i + 1, result + if isfref then Fref.oldsym else oldsym, modpara, org, calls + oldsym, newsource, tempX)
   else
    let k = lookup(dict, name.oldsym, paratypes.oldsym)
     assert cardinality.k = 1 report"Cannot find template for" + name.oldsym + "("
     +  paratypes.oldsym @@ list("",",", print.@e) 
     + ")"
     + "while processing"
     + org
      assert not(oldsym = k_1)report"ERR12" + print.oldsym + print.k_1
      let dd = lookupcode(sourceX, k_1)
       if isdefined.dd then
       postbind3(alltypes, dict, code, i + 1, result + if isfref then Fref.k_1 else k_1, modpara, org, calls + k_1, sourceX, tempX)
       else
        // handles parameterized unbound cases like ?(int arc, int arc)graph.int"//
        handletemplates(alltypes, dict, code, i, result, isfref, k_1, modpara, org, calls, sourceX, tempX)

function codeforbuiltin(alltypes:typedict, newsym:symbol, oldsym:symbol, org:seq.word)seq.symbol
 let newmodpara = parameter.modname.newsym
 if fsig.oldsym = "setfirst(T seq,int,int)"  then
  [Local.1,Local.2,Local.3,symbol("setfirst(int seq,int,int)","builtin","int seq")]
  else if fsig.oldsym = "allocatespace:T(int)" then [Local.1,symbol("allocatespace(int)","builtin","int seq")]
  else if fsig.oldsym = "sizeoftype:T"then [ Lit.size.gettypeinfo(alltypes, newmodpara)]
  else if fsig.oldsym = "processresult(T process)"then
  [ Local.1, Lit.2, Idx.kind.gettypeinfo(alltypes, newmodpara)]
  else if fsig.oldsym = "packed(T seq)"then
    [Local.1]+blocksym.gettypeinfo(alltypes, newmodpara)
  else if fsig.oldsym = "primitiveadd(T encodingpair)"then
  let addefunc = newsymbol("add", typeencoding + newmodpara, [ typeencodingstate + newmodpara, typeencodingpair + newmodpara], typeencodingstate + newmodpara)
   let add2 = newsymbol("addencoding", mytype."builtin", [ typeint, mytype."int seq", typeint, typeint], typeint)
   let dc = deepcopysym(alltypes, typeencodingpair + newmodpara)
    encodenocode.newmodpara + [ Local.1, Fref.addefunc, Fref.dc, add2, Words."NOINLINE STATE", Optionsym]
  else
   assert fsig.oldsym = "getinstance:encodingstate.T"report"not expecting" + print.oldsym
   let get = symbol("getinstance(int)","builtin","ptr")
    encodenocode.newmodpara + [ get, Words."NOINLINE STATE", Optionsym]

function  blocksym(info:typeinfo) seq.symbol
 let ds = size.info
    if kind.info="real"_1 then 
      [   symbol("blockit(real seq)","assignencodingnumber","real seq")]
    else  if ds = 1 then [  symbol("blockit(int seq)","assignencodingnumber","int seq")]
    else [ Lit.ds, symbol("blockit( char seq encodingpair seq,int)","assignencodingnumber","char seq encodingpair seq")]
   
 

function encodenocode(typ:mytype)seq.symbol
 let gl = symbol("global" + print.typ,"builtin","int seq")
 let setfld = symbol("setfld(int,T seq,   T)"," int builtin","int")
 let encodenosym = newsymbol("encodingno", mytype."assignencodingnumber", [ mytype."word seq"], typeint)
 let IDXI = Idx."int"_1
  if typ = mytype."typename"then [ Lit.0, gl,  Lit.2, setfld, Define."xx", gl, Lit.0, IDXI]
  else if typ = mytype."char seq"then
  [ Lit.0, gl,  Lit.1, setfld, Define."xx", gl, Lit.0, IDXI]
  else
   [ gl, Lit.0, IDXI, Lit.0, EqOp, Lit.3, Lit.2, Br, gl, Lit.0
   , IDXI, Exit, Lit.0, gl,  Words.typerep.typ, encodenosym, setfld, Define."xx", gl, Lit.0
   , IDXI, Exit, Block(typeint, 3)]

function definedeepcopy(alltypes:typedict, type:mytype, org:seq.word)seq.symbol
 if abstracttype.type in "encoding int word"then [ Local.1]
 else if abstracttype.type = "seq"_1 then
 let ds = size.gettypeinfo(alltypes, type)
 let info=gettypeinfo(alltypes, parameter.type)
  let kind = kind.info
  let typepara = if kind in "int real"then mytype.[ kind]else parameter.type
  let seqtype = typeseq + typepara
  let dc = deepcopysym(alltypes, typepara)
   let cat = newsymbol("+", seqtype, [ seqtype, typepara], seqtype)
  let resulttype = mytype."ptr"
  let elementtype = mytype.[ kind]
     let symEle=newsymbol("@e",abstracttype("builtin"_1,parameter.seqtype),empty:seq.mytype,parameter.seqtype)
    let symAcc=newsymbol("@acc",abstracttype("builtin"_1,parameter.seqtype),empty:seq.mytype,resulttype)
   [Local.1]+Emptyseq+[Local.1,symAcc,  symEle, dc,cat   , Lit.size.info    
   , newsymbol("apply3", abstracttype("builtin"_1, resulttype), [ seqtype, resulttype, seqtype, resulttype, typeint]
, resulttype)]
   + // if ds = 1 then 
     [ symbol("blockit(int seq)","assignencodingnumber","int seq")]
   else [ Local.1, Lit.ds, symbol("packed(int seq seq, ds)","assignencodingnumber","int seq")] //
     blocksym.info
 else
  let typedesc = gettypeinfo(alltypes, type)
  let y = subfld(alltypes, subflds.typedesc, 1,"", empty:seq.symbol)
   if size.typedesc = 1 then
   // only one element in record so type is not represent by actual record //
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