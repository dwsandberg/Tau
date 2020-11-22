module postbind


use seq.mytype

use stdlib

use seq.symbol

use set.symbol

use symbol

use seq.typeinfo

/function print3(s:symbol)seq.word if(zcode.s)_1 = s then print.s else print.s +"->"+ print.(zcode.s)_1 + if length.zcode.s = 1 then"NO CODE"else""

Function postbind(alltypes:typedict, dict:set.symbol, roots:seq.symbol,  theprg:program, templates:program)program
  let root = newsymbol("Wroot", mytype."W", empty:seq.mytype, typeint)
   postbind(alltypes , dict , empty:set.symbol, [root], 1,emptyprogram , map(theprg, root, roots) , templates ) 
  


function postbind(alltypes:typedict, dict:set.symbol, working:set.symbol, toprocess:seq.symbol, i:int, result:program, sourceX:program, tempX:program)program
 // assert true report @(seperator."
&br", print3,"", toseq.toset.tempX)//
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
        , if length.toprocess = 1
        ∧ toprocess_1 = newsymbol("Wroot", mytype."W", empty:seq.mytype, typeint)then
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
   let a = Block(mytype.[kind(alltypes, modpara, resulttype.sym)], nopara.sym)
     postbind3(alltypes, dict, code, i + 1, result + if isfref then Fref.a else a, modpara, org, calls, sourceX, tempX)
   else if isapply.sym then
   let newapply = Apply(nopara.sym, [ kind.gettypeinfo(alltypes, replaceT(modpara, parameter.modname.sym))], [ kind.gettypeinfo(alltypes, replaceT(modpara, resulttype.sym))])
     postbind3(alltypes, dict, code, i + 1, result + newapply, modpara, org, calls, sourceX, tempX)
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
      if (fsig.sym)_1 in  "offsets"then
       // symbol( offset(<rettype> <types with unknownsize > ,<knowoffset>+"builtin",<rettype>) //
       let paratypes=paratypes.sym
       let offset = @(+, Size(alltypes,modpara), toint.(module.sym)_1,subseq(paratypes,2,length.paratypes) )
        let resultinfo = gettypeinfo(alltypes, replaceT(modpara, resulttype.sym))
        let p2 = if size.resultinfo = 1 then 
                   [ Lit.offset, Idx.kind.resultinfo]
                else
                  [ Lit.offset, Lit.size.resultinfo, symbol("cast(T seq, int, int)","builtin","ptr")]
       postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
      else if(fsig.sym)_1 in "build"then
       let c=@(+,subflds(alltypes,modpara),empty:seq.seq.mytype, paratypes.sym)
        let p2 = buildconstructor(alltypes,if i = 2 then // for seq index func //   "int" else "", c
        , "", 1, 1, 0, empty:seq.symbol)
         postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
      else if(fsig.sym)_1 in "kindrecord"then
      let p2 = Record.@(+, kind(alltypes, modpara), "", paratypes.sym)
        postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls, sourceX, tempX)
      else
       let codeforbuiltin = codeforbuiltin(alltypes, newsym, sym, org)
        postbind3(alltypes, dict, code, i + 1, result + if isfref then Fref.newsym else newsym, modpara, org, calls + newsym, map(sourceX, newsym, codeforbuiltin), tempX)
     else if subseq(fsig.sym,1,2)="type:" then
      let p2=definedeepcopy(alltypes, resulttype.newsym,org)
     // assert false report "XXX"+print.newsym //
      postbind3(alltypes, dict, code, i + 1, result + if isfref then Fref.newsym else newsym, modpara, org, calls + newsym, map(sourceX, newsym, p2), tempX)
   else   
     handletemplates(alltypes, dict, code, i, result, isfref, newsym, modpara, org, calls, sourceX, tempX)

function kind(alltypes:typedict, with:mytype, a:mytype) word  kind.gettypeinfo(alltypes, replaceT(with, a))

function kind(alltypes:typedict,   a:mytype) word  kind.gettypeinfo(alltypes,   a )


function subflds(alltypes:typedict, with:mytype, a:mytype) seq.mytype subflds.gettypeinfo(alltypes, replaceT(with, a)) 

   use seq.seq.mytype

function Size(alltypes:typedict, with:mytype, a:mytype) int size.gettypeinfo(alltypes, replaceT(with, a)) 
 

function buildconstructor(alltypes:typedict,addfld:seq.word, flds:seq.seq.mytype, flatflds:seq.word, fldno:int, j:int, subfld:int, result:seq.symbol)seq.symbol
 // assert [ fldno, j, subfld, length.flatflds]in [ [ 1, 1, 0, 0], [ 2, 2, 0, 1], [ 2, 3, 1, 4], [ 2, 4, 2, 4], [ 3, 5, 0, 4]]report @(+, toword,"jkl", [ fldno, j, subfld, length.flatflds, length.flds])//
 if fldno > length.flds then result + Record(addfld + flatflds)
 else
  let fldsubfields = flds _fldno 
  let newflatflds = if j > length.flatflds then flatflds + @(+,kind.alltypes,"",fldsubfields) else flatflds
  let newresult = result
  + if length.fldsubfields = 1 then [ Local.fldno] else [ Local.fldno, Lit.subfld, Idx.newflatflds_j]
   if subfld = length.fldsubfields - 1 then 
        buildconstructor(alltypes,addfld, flds, newflatflds, fldno + 1, j + 1, 0, newresult)
   else buildconstructor(alltypes,addfld, flds, newflatflds, fldno, j + 1, subfld + 1, newresult)

function handletemplates(alltypes:typedict, dict:set.symbol, code:seq.symbol, i:int, result:seq.symbol, isfref:boolean, oldsym:symbol, modpara:mytype, org:seq.word, calls:set.symbol
, sourceX:program, tempX:program)resultpb
 assert not(last.module.oldsym = "builtin"_1)report"ISb" + print.oldsym
  assert not("T"_1 in fsig.oldsym) ∧ not((module.oldsym)_1 = "T"_1)
  ∧ not((returntype.oldsym)_1 = "T"_1)report"has T" + print.oldsym
  let fx = lookupcode(tempX, oldsym)
   if isdefined.fx then
   let newsource = if isdefined.lookupcode(sourceX, oldsym)then sourceX else map(sourceX, oldsym, code.fx)
     postbind3(alltypes, dict, code, i + 1, result + if isfref then Fref.oldsym else oldsym, modpara, org, calls + oldsym, newsource, tempX)
   else
    let k = lookup(dict, name.oldsym, paratypes.oldsym)
     assert cardinality.k = 1 report"Cannot find template for" + name.oldsym + "("
     + @(seperator.",", print,"", paratypes.oldsym)
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

use seq.myinternaltype

function codeforbuiltin(alltypes:typedict, newsym:symbol, oldsym:symbol, org:seq.word)seq.symbol
 let newmodpara = parameter.modname.newsym
  if fsig.oldsym = "sizeoftype:T"then [ Lit.size.gettypeinfo(alltypes, newmodpara)]
  else if fsig.oldsym = "processresult(T process)"then
  [ Local.1, Lit.2, Idx.kind.gettypeinfo(alltypes, newmodpara)]
  else if fsig.oldsym = "callidx(T seq, int)"then
  [ Local.1, Local.2, Callidx.kind.gettypeinfo(alltypes, newmodpara)]
  else if fsig.oldsym = "packed(T seq)"then
  let ds = size.gettypeinfo(alltypes, newmodpara)
    if ds = 1 then [ Local.1, symbol("packed1(int seq)","assignencodingnumber","int seq")]
    else [ Lit.ds, Local.1, symbol("packed(int, int seq seq)","assignencodingnumber","int seq")]
  else  if fsig.oldsym = "assert(word seq)"then
  let kind = kind.gettypeinfo(alltypes, resulttype.newsym)
   let codesym = if kind = "int"_1 then symbol("assert(word seq)","builtin","int")
   else if kind = "real"_1 then symbol("assertreal(real seq)","builtin","real")
   else symbol("assertptr(word seq)","builtin","ptr")
    [ Local.1, codesym]
    else  if fsig.oldsym = "primitiveadd(T encodingpair)"then
  let addefunc = newsymbol("add", typeencoding+newmodpara  ,   [ typeencodingstate+newmodpara , typeencodingpair+newmodpara ] ,  typeencodingstate+newmodpara )
    let add2=newsymbol("addencoding",mytype."builtin",[typeint,mytype("int seq"),typeint, typeint], typeint)
       let dc=deepcopysym(alltypes,typeencodingpair+newmodpara)
        encodenocode.newmodpara + [ Local.1, Fref.addefunc, Fref.dc, add2, Words."NOINLINE STATE", Optionsym]
  else
   assert fsig.oldsym = "getinstance:encodingstate.T"report"not expecting" + print.oldsym
   let get = symbol("getinstance(int)","builtin","ptr")
    encodenocode.newmodpara + [ get, Words."NOINLINE STATE", Optionsym]

function encodenocode(typ:mytype)seq.symbol
 let gl = symbol("global" + print.typ,"builtin","int seq")
 let setfld = symbol("setfld(int seq, int, int)","builtin","int")
 let encodenosym = newsymbol("encodingno", mytype."assignencodingnumber", [ mytype."word seq"], typeint)
 let IDXI = Idx."int"_1
  if typ = mytype."typename"then [ gl, Lit.0, Lit.2, setfld, Define."xx", gl, Lit.0, IDXI]
  else if typ = mytype."char seq"then
  [ gl, Lit.0, Lit.1, setfld, Define."xx", gl, Lit.0, IDXI]
  else
   [ gl, Lit.0, IDXI, Lit.0, EqOp, Lit.3, Lit.2, Br, gl, Lit.0
   , IDXI, Exit, gl, Lit.0, Words.typerep.typ, encodenosym, setfld, Define."xx", gl, Lit.0
   , IDXI, Exit, Block(typeint, 3)]

function definedeepcopy(alltypes:typedict, type:mytype, org:seq.word)seq.symbol
 if abstracttype.type in "encoding int word"then [ Local.1]
 else if abstracttype.type = "seq"_1 then
 let ds = size.gettypeinfo(alltypes, type)
  let kind = kind.gettypeinfo(alltypes, parameter.type)
  let typepara = if kind in "int real"then mytype.[ kind]else parameter.type
  let seqtype = typeseq+ typepara  
  let dc = deepcopysym(alltypes,typepara)
  let pseqidx = pseqidxsym.typepara
  let cat = newsymbol("+", seqtype, [ seqtype, typepara], seqtype)
   Emptyseq + [ Local.1, Fref.dc, Fref.cat, Fref.pseqidx, Apply(5, [ kind],"ptr")]
   + if ds = 1 then [ symbol("packed1(int seq)","assignencodingnumber","int seq")]
   else [ Local.1, Lit.ds, symbol("packed(int seq seq, ds)","assignencodingnumber","int seq")]
 else
  let typedesc = gettypeinfo(alltypes, type)
  let y = subfld(alltypes,subflds.typedesc, 1,"", empty:seq.symbol)
   if size.typedesc = 1 then
   // only one element in record so type is not represent by actual record // [ Local.1]
    + subseq(y, 4, length.y - 1)
   else
    assert size.typedesc ≠ 1 report"Err99a" + print.type
     y

function subfld(alltypes:typedict,flds:seq.mytype, fldno:int,fldkinds:seq.word, result:seq.symbol)seq.symbol
 if fldno > length.flds then result + [ Record.fldkinds]
 else
  let fldtype = flds_fldno
  let kind=kind.gettypeinfo(alltypes,fldtype)
   subfld(alltypes,flds, fldno + 1,fldkinds+kind, result + [ Local.1, Lit(fldno - 1), Idx.kind, deepcopysym(alltypes,fldtype)])