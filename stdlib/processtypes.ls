Module processtypes

use graph.libtype

use libscope


use seq.arc.libtype

use set.arc.libtype

use seq.libsym

use seq.libtype

use seq.mytype

use set.libtype

/use seq.word

use stdlib

type libtype is record name:word, abstract:boolean, kind:word, subtypes:seq.mytype, size:offset, fldnames:seq.word

Function =(a:libtype, b:libtype)boolean name.a = name.b ∧ abstract.a = abstract.b

Function abstract(libtype)boolean export

Function name(libtype)word export

Function fortype(l:libtype)mytype 
 mytype.if abstract.l then"T"+ name.l else [ name.l]

Function subtypes(libtype)seq.mytype export

Function kind(libtype)word export

Function libtype(word, boolean, word, seq.mytype, offset, seq.word)libtype export

Function fldnames(libtype)seq.word export

Function size(libtype)offset export


Function ?(a:arc.libtype, b:arc.libtype)ordering export


Function print(a:libtype)seq.word 
 [ name.a]+(if abstract.a then".T"else"")+"size"+ print.size.a +"kind"+ kind.a + @(+, print,"", subtypes.a)

Function ?(a:libtype, b:libtype)ordering 
 let t = name.a ? name.b 
  if t = EQ then abstract.a ? abstract.b else t

function addnodup(a:set.libtype, b:libtype)set.libtype 
 if isinstance.fortype.b 
  then a 
  else let size = if abstracttype.fortype.b in"seq encoding"∨ kind.b in"type sequence"
   then offset.1 
   else offset.0 
  let c = a + b 
  assert cardinality.c > cardinality.a report"type"+ print.fortype.b +"is defined twice"
  c

Function assigntypesizes(f:seq.libtype)set.libtype 
 let init = empty:seq.libtype 
  let a = @(addnodup, identity, asset.init, f)+ libtype("T"_1, false,"struct"_1, empty:seq.mytype, offset.0,"")
  // assert false report @(lines, print,"", toseq.a)// 
  // build dependence graph for types.It should be acyclic // 
 //  let discard = if false then arc(f_1,f_1) ? arc(f_1,f_1) else EQ //
  let g = newgraph.@(+, getarcs.a, empty:seq.arc.libtype, toseq.a)
  let c = sinksfirst.g 
  // assert false report @(lines, print,"", c)// 
  let cyclic = asset.c - nodes.g 
  assert isempty.cyclic report"cyclic type def"
  @(sizetype, identity, asset.empty:seq.libtype, c + toseq(asset.f - asset.c))

function lookup(name:word, abstract:boolean, s:set.libtype, message:seq.word)libtype 
 let e = findelement(libtype(name, abstract,"X"_1, empty:seq.mytype, offset.0,""), s)
  assert not.isempty.e report"type"+ name +"not defined"+ message 
  e_1

function getarcs(s:set.libtype, message:seq.word, node:libtype, typ:mytype)seq.arc.libtype 
 getarcs(s, message, node, typ, length.towords.typ)

function getarcs(s:set.libtype, message:seq.word, node:libtype, typ:mytype, i:int)seq.arc.libtype 
 let n = lookup(towords(typ)_i, i > 1, s, message)
  if i = 1 ∨ not(size.n = offset.0)∨ name.n ="encoding"_1 
  then [ arc(node, n)]
  else getarcs(s, message, n, typ, i - 1)+ arc(node, n)

function getarcs(s:set.libtype, t:libtype)seq.arc.libtype 
 @(+, getarcs(s,"", t), empty:seq.arc.libtype, subtypes.t)

function sizetype(s:set.libtype, t:libtype)set.libtype 
 if size.t = offset.0 
  then s + libtype(name.t, abstract.t, kind.t, subtypes.t, @(+, sizeoftype.s, offset.0, subtypes.t), fldnames.t)
  else s + t

Function deepcopytypes2(all:set.libtype, t:mytype)seq.mytype 
 // deepcopytypes is only for structures.It returns the types of the fields.If one of the fields is a structure it returns the types of that structure to flatten out the struct into a sequence of fields of size 1.// 
  let b = lookup(abstracttype.t, iscomplex.t, all,"Unknown error in process types!")
  if kind.b in"type sequence"∨ towords.t ="word"
  then [ t]
  else @(+, deepcopytypes2.all, empty:seq.mytype, if isinstance.t then @(+, replaceT.parameter.t, empty:seq.mytype, subtypes.b)else subtypes.b)

Function deepcopytypes3(all:set.libtype, t:mytype)seq.mytype 
 // deepcopytypes is only for structures.It returns the types of the fields.If one of the fields is a structure it returns the types of that structure to flatten out the struct into a sequence of fields of size 1.// 
  let b = lookup(abstracttype.t, iscomplex.t, all,"Unknown error in process types!")
  if kind.b in"type sequence encoding"∨ towords.t in ["word", "int"] &or "T"_1 in towords.t
  then [ t]
  else @(+, deepcopytypes3.all, empty:seq.mytype, if isinstance.t then @(+, replaceT.parameter.t, empty:seq.mytype, subtypes.b)else subtypes.b)





Function fldsoftype(s:set.libtype, a:mytype)seq.mytype 
 let b = subtypes.lookup(abstracttype.a, iscomplex.a, s,"Unknown error in process types!")
  if isinstance.a then @(+, replaceT.parameter.a, empty:seq.mytype, b)else b

Function sizeoftype(s:set.libtype, a:mytype)offset 
 if a = mytype."T"
  then Tsize 
  else if abstracttype.a in"seq encoding"
  then offset.1 
  else let size = size.lookup(abstracttype.a, length.towords.a > 1, s,"Unknown error in process types!")
  if length.towords.a > 1 ∧ not(size = offset.1)then compose(size, sizeoftype(s, parameter.a))else size

Function libtypes(message:seq.word, alltypes:set.libtype, a:mytype)set.libtype 
 let l = lookup(abstracttype.a, iscomplex.a, alltypes, message)
  if abstract.l then libtypes(message, alltypes, parameter.a)+ l else asset.[ l]

Function libtypes(s:set.libtype, a:libsym)set.libtype 
 lookuptypes("type not found"+ fsig.a, s, syminfo.a)

Function lookuptypes(message:seq.word, s:set.libtype, d:syminfo)set.libtype 
 @(∪, libtypes(message, s), libtypes(message, s, returntype.d), paratypes.d)

Function libtypes(s:set.libtype, a:seq.libsym)set.libtype 
 @(∪, libtypes.s, empty:set.libtype, a) - libtypes("T type not found", s, mytype."T")

Function noparameters(l:libsym)int length.paratypes.syminfo.l

_______________________-

use newsymbol

Function +(a:mytype, w:word)mytype mytype(towords.a + w)

/Function ?(a:mytype, b:mytype)ordering 
 let y = towords(a)_length.towords.a ? towords(b)_length.towords.b 
  if y = EQ 
  then let x = length.towords.a ? length.towords.b 
   if x = EQ 
   then if length.towords.a = 2 ∧ towords(a)_1 ="T"_1 ∧ not(towords(b)_1 ="T"_1)
    then LT 
    else if length.towords.a = 2 ∧ towords(b)_1 ="T"_1 ∧ not(towords(a)_1 ="T"_1)
    then GT 
    else orderm(towords.a, towords.b, length.towords.a)
   else x 
  else y

/function orderm(a:seq.word, b:seq.word, i:int)ordering 
 if i = 1 
  then encoding(a_1)? encoding(b_1)
  else let x = encoding(a_i)? encoding(b_i)
  if x = EQ then orderm(a, b, i - 1)else x


/Function ?(a:seq.mytype, b:seq.mytype, i:int)ordering 
 let o1 = length.a ? length.b 
  if o1 = EQ ∧ length.a ≥ i 
  then let o2 = a_i ? b_i 
   if o2 = EQ then ?(a, b, i + 1)else o2 
  else o1

Function print(mytype)seq.word export

------------------

Function +(a:ordering, b:ordering)ordering if a = EQ then b else a

Function ?2(a:syminfo, b:syminfo)ordering 
 {(encoding.name.a ? encoding.name.b)+(length.paratypes.a ? length.paratypes.b)+(?(paratypes.a, paratypes.b, 1))}

Function ?(a:syminfo, b:syminfo)ordering 
 let o1 = ?2(a, b)
  if o1 = EQ then modname.a ? modname.b else o1

Function actualreturntype(s:syminfo)mytype 
 if isinstance.modname.s then replaceT(parameter.modname.s, returntype.s)else returntype.s

Function print(a:syminfo)seq.word formatcall(modname.a, name.a, paratypes.a)+ print.returntype.a

Function print0(a:syminfo)seq.word formatcall(name.a, paratypes.a)+ print.returntype.a

Function funcfrominstruction(alltypes:set.libtype, instruction:seq.word, returntype:mytype, nopara:int)seq.word 
 // assumes not for abstract symbol // 
  if length.instruction = 0 
  then"USECALL PARAM 1"
  else if instruction_1 ="USECALL"_1 
  then instruction 
  else assert not(instruction_1 in"ERECORD BUILDSEQ")report"not expecting"+ instruction 
  {"USECALL"+ if instruction_1 ="BUILD"_1 
   then if sizeoftype(alltypes, returntype)= offset.nopara 
    then paralistcode.nopara +"RECORD"+ toword.nopara 
    else flattenrecord(alltypes, fldsoftype(alltypes, returntype), 1,"", offset.0)
   else paralistcode.nopara + instruction }

function flattenrecord(alltypes:set.libtype, ptypes:seq.mytype, i:int, result:seq.word, total:offset)seq.word 
 // care is taken to make sure resulting procedure can be recognized as one that can be expanded inline // 
  if i > length.ptypes 
  then result +"RECORD"+ toword.length.ptypes 
  else let sz = sizeoftype(alltypes, ptypes_i)
  let flatinst = if sz = offset.1 then""else"FLAT"+ print.sz 
  flattenrecord(alltypes, ptypes, i + 1,  result +"PARAM"+toword.i+ flatinst, total + sz)

Function paralistcode(nopara:int)seq.word @(+, makepara,"", arithseq(nopara, 1, 1))

function makepara(i:int)seq.word  {"PARAM"+ toword.i } 

Function replaceTsyminfo(within:mytype, s:syminfo)syminfo 
 if not.hasproto.s ∧ not.isabstract.modname.s 
  then s 
  else let with = if hasproto.s then replaceT(within, parameter.modname.s)else within 
  if hasproto.s 
  then assert isabstract.protomodname.s report"expected abstract proto"
   syminfoinstance(with, protoname.s, protomodname.s, protoparatypes.s, protoreturntype.s,"USECALL")
  else syminfoinstance(with, name.s, modname.s, paratypes.s, returntype.s, instruction.s)

function syminfoinstance(with:mytype, name:word, modname:mytype, paratypes:seq.mytype, returntype:mytype, instruction:seq.word)syminfo 
 let namex = if length.paratypes > 0 then name else replaceT(with, name)
  syminfoinstance(namex, replaceT(with, modname), @(+, replaceT.with, empty:seq.mytype, paratypes), replaceT(with, returntype), instruction, name, paratypes, returntype)

______________________


type offset is record TSIZE:int, LIT:int

Function LIT(offset)int export

Function TSIZE(offset)int export


Function Tsize offset offset(1, 0)

Function offset(i:int)offset offset(0, i)

Function =(a:offset, b:offset)boolean TSIZE.a = TSIZE.b ∧ LIT.a = LIT.b

Function print(a:offset)seq.word 
 [ toword.LIT.a]+ if TSIZE.a = 0 then""else"TSIZE"+ toword.TSIZE.a

Function +(a:offset, b:offset)offset offset(TSIZE.a + TSIZE.b, LIT.a + LIT.b)

Function +(s:seq.int, b:offset)seq.int s + LIT.b

Function compose(a:offset, b:offset)offset offset(TSIZE.a * TSIZE.b, TSIZE.a * LIT.b + LIT.a)
