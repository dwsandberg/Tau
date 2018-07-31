module pass1a

type r3 is record code:seq.word, types:seq.mytype, nexttemp:int

use definestruct

use libscope

use oseq.libsym

use pass0

use passcommon

use real

use seq.func

use seq.int

use seq.libmod

use seq.libsym

use seq.libtype

use seq.mod2desc

use seq.mytype

use seq.pass1result

use seq.r3

use seq.seq.mod2desc

use seq.seq.word

use seq.syminfo

use seq.tree.word

use seq.word

use set.libtype

use set.mod2desc

use set.syminfo

use set.word

use stdlib

use processtypes

use tree.word

Function =(a:r3, b:r3)boolean false

type symdict is record text:seq.word, syminfos:set.syminfo, alltypes:set.libtype, bindingonly:boolean

Function fortext(d:symdict)seq.word prettytext.text.d

prettytree(defaultcontrol, parse(text.d, tree("X"_1)))

Function findsymbol(d:symdict, w:word, types:seq.mytype)syminfo 
 let e = findelement2(syminfos.d, syminfo(w, types))
  // assert false report @(lines, print,"", toseq.syminfos.d)// 
  if cardinality.e > 1 ∧ subseq(instruction(e_1), 1, 1)="UNBOUND"
  then e_1 
  else assert cardinality.e = 1 report if cardinality.e > 0 
   then"Multi definition for symbol"+ formatcall(w, types)+"found in"+ @(+, print,"", @(+, modname, empty:seq.mytype, toseq.e))
   else"Symbol"+ formatcall(w, types)+"NOT FOUND in:"+ fortext.d 
  e_1

function noparameters(s:syminfo)int length.paratypes.s

Function findseqindexfunction(d:symdict, type:mytype)syminfo 
 let sym = findsymbol(d,"_"_1, [ type, mytype."int"])
  assert returntype.sym = parameter.type report"return type of"+ formatcall(name.sym, paratypes.sym)+"is not"+ print.type +"as expected."
  sym

Function find(d:symdict, w:word, l:seq.r3)r3 
 let typelist = @(+, types, empty:seq.mytype, l)
  let sym = findsymbol(d, w, typelist)
  let noparameters = length.paratypes.sym 
  if bindingonly.d 
  then // assert not(hasproto.sym ∧ noparameters = 0)∨ returntype.sym in [ mytype."T treenode seq"]report"X"+ name.sym + print.returntype.sym + @(+, print,"", paratypes.sym)+ mangled.sym + @(+, print,"TYPELIST", typelist)// 
   if length.instruction.sym > 0 ∧ instruction(sym)_1 ="TYPESIZE"_1 
   then r3("TYPESIZE 0", [ mytype."int"], nexttemp(l_length.l))
   else r3(@(+, code,"", l)+ mangled.sym + toword.noparameters, [ returntype.sym], nexttemp(l_length.l))
  else let code = if isinstance.modname.sym 
   then if"TSIZE"_1 in instruction.sym then"USECALL"else instruction.sym 
   else if not.isabstract.modname.sym ∧ subseq(instruction.sym, 1, 1)="BUILD"
   then"USECALL"
   else instruction.sym 
  let nexttmp = nexttemp(l_length.l)
  let codesons = @(+, code,"", l)
  if length.code = 0 
  then r3(codesons, [ returntype.sym], nexttmp)
  else if code_1 in"USECALL UNBOUND"
  then // assert CALLcode.sym = CALLcode.(sym)report"DIFFX"+ CALLcode.sym + CALLcode.(sym)// 
   let z = [ if isabstract.modname.sym then"CALLB"_1 else"CALL"_1, 
   toword.noparameters, 
   mangled.sym]
   r3(codesons + z, [ returntype.sym], nexttmp)
  else if code_1 ="BUILDSEQ"_1 
  then r3(FREFcode.findseqindexfunction(d, returntype.sym)+ codesons +"RECORD"+ toword(toint(code_2)+ 1), [ returntype.sym], nexttmp)
  else if code_1 in"ERECORD PRECORD"
  then let basetype = parameter.returntype.sym 
   r3(codesons + if isabstract.basetype then CALLcode.sym else codingrecord.sym, [ returntype.sym], nexttmp)
  else if code_1 ="BUILD"_1 
  then let r = fixuprecord(alltypes.d, l, noparameters, nexttmp, 1,"", offset.0)
   r3(code.r, [ returntype.sym], nexttemp.r)
  else if code_1 ="TYPESIZE"_1 
  then r3("LIT"+ print.sizeoftype(alltypes.d, returntype.sym), [ mytype."int"], nexttmp)
  else if code_1 ="FROMSEQ"_1 
  then let locvar = toword.nexttmp 
   let f1 = codesons +"LOCAL"+ locvar +"LIT 0 IDXUC 2"+ FREFcode.findseqindexfunction(d, returntype.sym)+"EQL 2 LOCAL"+ locvar +"LIT 0 LIT 0 RECORD 2 if 3 SET"+ locvar 
   r3(f1, [ returntype.sym], nexttmp + 1)
  else r3(codesons + code, [ returntype.sym], nexttmp)

function fixuprecord(alltypes:set.libtype, l:seq.r3, nopara:int, nextvar:int, i:int, result:seq.word, total:offset)r3 
 // make sure all parameters to RECORD are LIT LOCAL PARA FREF and then expand records to single words before building the record // 
  // may change order of eval? // 
  if i > nopara 
  then r3(result +"RECORD"+ toword.nopara, empty:seq.mytype, nextvar)
  else let r = l_i 
  let sz = sizeoftype(alltypes, types(r)_1)
  let flatinst = if sz = offset.1 then""else"FLAT"+ print.sz 
  if length.code.r = 2 ∧ code(r)_1 in"LIT LOCAL PARA FREF FREFB"
  then fixuprecord(alltypes, l, nopara, nextvar, i + 1, result + code.r + flatinst, total + sz)
  else let f = fixuprecord(alltypes, l, nopara, nextvar + 1, i + 1, result +"LOCAL"+ toword.nextvar + flatinst, total + sz)
  r3(code.r + code.f +"SET"+ toword.nextvar, types.f, nexttemp.f)

Function wordcode(t:tree.word)seq.word {"WORD"+ label.t }

Function checkassert(d:symdict, c:r3, t:r3, e:r3)r3 
 assert types(c)_1 = mytype."boolean"report"condition in assert must be boolean in:"+ fortext.d 
  assert types(e)_1 = mytype."word seq"report"else in assert must be seq of word in:"+ fortext.d 
  r3(code.c + code.t + code.e + if bindingonly.d then"assert 3"else"assertZbuiltinZwordzseq 1 if 3", types.t, nexttemp.e)

function addlocal(d:symdict, name:word, exp:r3, t:tree.word)r3 
 FORCEINLINE.let nexttmp = nexttemp.exp 
  let arg = toword.nexttmp 
  let e = syminfo(name, mytype."local", empty:seq.mytype, types(exp)_1,"LOCAL"+ arg)
  assert not(e in syminfos.d)report"local"+ name +"conflicts with previous declaration in:"+ fortext.d 
  let newdict = symdict(text.d, syminfos.d + e, alltypes.d, bindingonly.d)
  let r = bind(newdict, t, nexttmp + 1)
  if bindingonly.d 
  then r3("WORD"+ name + code.exp + code.r +"let 3", types.r, nexttemp.r)
  else r3(code.exp + code.r +"SET"+ arg, types.r, nexttemp.r)

function bindsons(d:symdict, t:tree.word, nexttmp:int)r3 
 let l = bindsonslist(d, t, nexttmp)
  let last = nexttemp(l_length.l)
  let codesons = @(+, code,"", l)
  let types = @(+, types, empty:seq.mytype, l)
  r3(codesons, types, last)

function bindsonslist(d:symdict, t:tree.word, nexttmp:int)seq.r3 bindsonslist(d, t, nexttmp, 1)

function bindsonslist(d:symdict, t:tree.word, nexttmp:int, i:int)seq.r3 
 if i > nosons.t 
  then // if there are no sons then return"empty"r3 with nexttemp set correctly // 
   [ r3("", empty:seq.mytype, nexttmp)]
  else let r = bind(d, t_i, nexttmp)
  [ r]+ bindsonslist(d, t, nexttemp.r, i + 1)

function isnumber(w:word)boolean isnumber(decode.w, 1)

function isnumber(l:seq.int, i:int)boolean 
 if length.l = 0 
  then false 
  else if i > length.l 
  then true 
  else if i = 1 ∧ l_1 = hyphenchar ∧ length.l > 1 
  then isnumber(l, 2)
  else if between(l_i, 48, 57)∨ l_i = nbspchar then isnumber(l, i + 1)else false

Function bind(d:symdict, t:tree.word, nexttmp:int)r3 
 if isnumber.label.t 
  then r3(["LIT"_1, label.t], [ mytype."int"], nexttmp)
  else if nosons.t = 3 ∧ label.t ="if"_1 
  then let c = bind(d, t_1, nexttmp)
   assert types(c)_1 = mytype."boolean"report"condition in if must be boolean in:"+ fortext.d 
   let th = bind(d, t_2, nexttemp.c)
   let el = bind(d, t_3, nexttemp.th)
   assert types(th)_1 = types(el)_1 report"then and else clause must have same type in:"+ fortext.d 
   r3(code.c + code.th + code.el +"if 3", types.el, nexttemp.el)
  else if nosons.t = 3 ∧ label.t ="assert"_1 
  then let c = bind(d, t_1, nexttmp)
   assert types(c)_1 = mytype."boolean"report"condition in assert must be boolean in:"+ fortext.d 
   let th = bind(d, t_2, nexttemp.c)
   let el = bind(d, t_3, nexttemp.th)
   checkassert(d, c, th, el)
  else if nosons.t = 3 ∧ label.t ="let"_1 
  then addlocal(d, label(t_1), bind(d, t_2, nexttmp), t_3)
  else if label.t ="$build"_1 
  then let r = bindsons(d, t, nexttmp)
   assert @(∧, =(types(r)_1), true, types.r)report"types do not match in build"+ fortext.d 
   r3(code.r + label.t + toword.nosons.t, [ types(r)_1 +"seq"_1], nexttemp.r)
  else if label.t ="$wordlist"_1 
  then r3(@(+, wordcode,"", sons.t)+ label.t + toword.nosons.t, [ mytype."word seq"], nexttmp)
  else if label.t ="@"_1 
  then checkapplyA(d, t, nexttmp)
  else if label.t ="comment"_1 
  then let r = bind(d, t_1, nexttmp)
   if bindingonly.d 
   then let txt = @(+, wordcode,"", subseq(sons.t, 2, nosons.t))
    r3(code.r + txt +"comment"+ toword.nosons.t, types.r, nexttemp.r)
   else bind(d, t_1, nexttmp)
  else if label.t in"process"
  then assert nosons.t = 1 report"process must have one arg"
   if bindingonly.d 
   then let c = bind(d, t_1, nexttmp)
    r3(code.c +"process 1", [ types(c)_1 +"process"_1], nexttemp.c)
   else let l = bindsonslist(d, t_1, nexttmp)
   let sym = findsymbol(d, label(t_1), @(+, types, empty:seq.mytype, l))
   let noargs = noparameters.sym 
   r3(FREFcode.finddeepcopyfunction.returntype.sym + 
   FREFcode.finddeepcopyfunction.mytype."word seq"+ FREFcode.sym +"LIT"+ toword.noargs + @(+, code,"", l)+
   "RECORD"+ toword(noargs + 4)+"PROCESS2 1", [ returntype.sym +"process"_1], nexttemp(l_length.l))
  else if nosons.t = 0 
  then find(d, label.t, bindsonslist(d, t, nexttmp))
  else if label.t ="makereal"_1 ∧ nosons.t = 2 ∧ isnumber.label(t_1)∧ isnumber.label(t_2)
  then if bindingonly.d 
   then r3("LIT"+ label(t_1)+"LIT"+ label(t_2)+"makereal 2", [ mytype."real"], nexttmp)
   else r3("LIT"+ toword.representation.makereal(toint.label(t_1), toint.label(t_2)), [ mytype."real"], nexttmp)
  else let l = bindsonslist(d, t, nexttmp)
  find(d, label.t, l)

Function checkapplyA(d:symdict, t:tree.word, nexttmp:int)r3 
 FORCEINLINE.assert nosons.t = 4 report"apply must have 4 terms"+ fortext.d 
  let term1 = t_1 
  let term1sons = bindsons(d, t_1, nexttmp)
  let term2 = t_2 
  let term2sons = bindsons(d, t_2, nexttemp.term1sons)
  let term3 = bind(d, t_3, nexttemp.term2sons)
  let term4 = bind(d, t_4, nexttemp.term3)
  assert abstracttype(types(term4)_1)="seq"_1 report"last argument of apply must be seq"+ fortext.d 
  let sym2 = findsymbol(d, label.term2, types.term2sons + [ parameter(types(term4)_1)])
  let sym1 = findsymbol(d, label.term1, types.term1sons + types.term3 + [ returntype.sym2])
  assert types(term3)_1 = returntype.sym1 report"term3 not same as init"
  let pseqtype = parameter(types(term4)_1)+"pseq"_1 
  if bindingonly.d 
  then r3(code.term1sons + mangled.sym1 + toword.nosons.term1 + code.term2sons + mangled.sym2 + toword.nosons.term2 + code.term3 + code.term4 +"@ 4", types.term3, nexttemp.term4)
  else r3(code.term1sons + code.term2sons + code.term3 + code.term4 + FREFcode.sym2 + FREFcode.sym1 + FREFcode.findseqindexfunction(d, pseqtype)+"APPLY"+ toword(nosons.term1 + nosons.term2 + 5), types.term3, nexttemp.term4)

Function bind(bindingonly:boolean, alltypes:set.libtype, modname:mytype, a:set.syminfo, text:seq.word)syminfo 
 let t = parse(text, tree("X"_1))
  let dict = symdict(text, a, alltypes, bindingonly)
  // will not return instructions containing ERECORD or BUILDSEQ. Returns augmented code // 
  // let cond = not(abstracttype.tomytype.modname in"invertedseq")∨ label.symbol.t in"= lookup ele"// 
  let sym = parsesyminfo(modname, text)
  let noparameters = length.paratypes.sym 
  if label.functionbody.t ="builtin"_1 
  then if bindingonly 
   then changeinstruction(sym,"USECALL builtin 0")
   else if nosons.functionbody.t = 0 
   then changeinstruction(sym,"USECALL PARA 1")
   else if instruction(sym)_1 ="BUILDSEQ"_1 
   then changeinstruction(sym,"USECALL"+ FREFcode.findseqindexfunction(dict, returntype.sym)+ paralistcode.noparameters +"RECORD"+ toword(toint(instruction(sym)_2)+ 1))
   else if instruction(sym)_1 in"ERECORD PRECORD"
   then changeinstruction(sym,"USECALL"+ codingrecord.sym)
   else sym 
  else let n = noparameters 
  let args = @(+, toword,"", arithseq(n, -1, n))
  // let dwithparameters = symdict(t, noparameters, paranames.t, paratypes.sym, args, syminfos.dict)// 
  let dwithparameters = symdict(text, @(+, makepara(paranames.t, paratypes.sym, args), syminfos.dict, arithseq(n, 1, 1)), alltypes.dict, bindingonly)
  let r = bind(dwithparameters, functionbody.t, 1)
  assert types(r)_1 = returntype.sym report"returntype does not match expression type for"+ print.sym 
  changeinstruction(sym,"USECALL"+ code.r)

Function makepara(paranames:seq.word, paratypes:seq.mytype, args:seq.word, i:int)syminfo 
 syminfo(paranames_i, mytype."local", empty:seq.mytype, paratypes_i,"PARA"+ args_i)

Function paranames(p:tree.word)seq.word @(+, label,"", subseq(sons.p, 3, nosons.p))


function isinstance(s:syminfo)set.word 
 if isinstance.modname.s 
  then let a = encode(libsym(returntype.s, mangled.s, instruction.s), libsymencoding)
   asset.[ mangled.s]
  else empty:set.word

Function pass1a(bindingonly:boolean, primitivemods:set.mod2desc, intemplates:seq.mod2desc, libname:seq.word)pass1result 
 let templatetypes = @(+, typedefs, empty:seq.libtype, intemplates)
  let P1 = toseq.primitivemods 
  let alltypes = assigntypesizes(@(+, typedefs, empty:seq.libtype, P1)+ templatetypes)
  let discard = @(+, checktypes.alltypes, 0, P1)
  let P2 = @(+, mergelocals.alltypes, empty:seq.mod2desc, P1)
  let PX = linkexports(asset(P2 + intemplates), P2)
  let allmods = asset(PX + intemplates)
  let PYA = @(+, compileabstract(bindingonly, alltypes, allmods), empty:seq.mod2desc, PX)
  let discard2 = @(+, processtemplate, empty:seq.syminfo, PYA)
  let alreadycompiled = @(+, processtemplate, empty:seq.syminfo, intemplates)
  let compiled = @(∪, isinstance, empty:set.word, alreadycompiled)
  let allsyms = allsymbols.allmods 
  let PYS = @(+, compilesimple(bindingonly, alltypes, allsyms, allmods), empty:seq.mod2desc, PX)
  let simplepairs = toseq.@(∪, defines, empty:set.syminfo, PYS)
  pass1result(libname, simplepairs, alreadycompiled, PYA + PYS, asset.templatetypes, alltypes)

the code for type func is never a code fragment and never abstract.

instructions for symbols are"USECALL"or a simple code fragment that can be turned into code by listing the code for the parameters and then appending the fragment.For abstract fragments appending is not enough to handle all fragments.

instructions for libsyms are a frag or begin with"USECALL"followed by the definition of the function

Function iscomplex(p:syminfo)seq.word 
 if isinstance.modname.p ∧ not.isabstract.modname.p then [ mangled.p]else""

Function complexexports(m:mod2desc)seq.word 
 // if isprivate.m then empty:seq.word else // @(+, iscomplex,"", toseq.export.m)

Function compilesimple(bindingonly:boolean, alltypes:set.libtype, allsyms:set.syminfo, allmods:set.mod2desc, thistype:mod2desc)seq.mod2desc 
 if isabstract.modname.thistype 
  then empty:seq.mod2desc 
  else // check to make sure all types are defined // 
  let syminfos = @(∪, expandexports.allmods, defines.thistype, uses.thistype)
  let a = @(+, bind(bindingonly, alltypes, modname.thistype, syminfos), empty:set.syminfo, tocompile.thistype)
  let def = @(+, funcfrominstruction.alltypes, a, toseq(defines.thistype - a))
  let functionsreferenced = @(∪, calls, asset.complexexports.thistype, toseq.def)
  let def2 = asset.@(+, compileinstance(alltypes, allsyms), empty:seq.syminfo, toseq.functionsreferenced)
  [ mod2desc(modname.thistype, export.thistype, empty:seq.mytype, typedefs.thistype, def ∪ def2, ["current"], isprivate.thistype)]

Function compileabstract(bindingonly:boolean, alltypes:set.libtype, allmods:set.mod2desc, thistype:mod2desc)seq.mod2desc 
 if not.isabstract.modname.thistype 
  then empty:seq.mod2desc 
  else // check to make sure all types are defined // 
  let syminfos = @(∪, expandexports.allmods, defines.thistype, uses.thistype)
  let a = @(+, bind(bindingonly, alltypes, modname.thistype, syminfos), empty:set.syminfo, tocompile.thistype)
  let def = @(+, funcfrominstruction.alltypes, a, toseq(defines.thistype - a))
  // let discard = @(+, encode, 0, toseq.defines.thistype)// 
  [ mod2desc(modname.thistype, export.thistype, empty:seq.mytype, typedefs.thistype, def, ["current"], isprivate.thistype)]

function funcfrominstruction(alltypes:set.libtype, b:syminfo)syminfo 
 if isabstract.modname.b 
  then b 
  else changeinstruction(b, funcfrominstruction(alltypes, instruction.b, actualreturntype.b, length.paratypes.b))

Function processtemplate(a:mod2desc)seq.syminfo 
 // encodes abstract syminfo and returns compiled syminfo // 
  if isabstract.modname.a 
  then let b = @(+, encode, 0, toseq.defines.a)
   empty:seq.syminfo 
  else toseq.defines.a

Function encode(t:syminfo)int 
 let i = encode(libsym(returntype.t, mangled.t, instruction.t), libsymencoding)
  0

--------------

