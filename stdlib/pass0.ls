module pass0

use definestruct

use libdesc

use libscope

use passcommon

use seq.libsym

use seq.libtype

use seq.mod2desc

use seq.moddesc

use seq.mytype

use seq.seq.seq.word

use seq.seq.word

use seq.syminfo

use set.mod2desc

use set.mytype

use set.syminfo

use stdlib

use tree.word

/use parse

Function ?(a:mod2desc, b:mod2desc)ordering 
 encoding.last.towords.modname.a ? encoding.last.towords.modname.b

function =(a:mod2desc, b:mod2desc)boolean modname.a = modname.b

Function template(name:mytype, defines:seq.syminfo, exports:seq.syminfo, types:seq.libtype)mod2desc 
 mod2desc(name, asset.exports, empty:seq.mytype, types, asset.defines, empty:seq.seq.word, false)

function addnodup(s:set.mod2desc, b:mod2desc)set.mod2desc 
 let c = s + b 
  assert cardinality.c > cardinality.s report"duplicate module name"+ print.modname.b 
  c

Function pass0(l:libdesc)set.mod2desc 
 // This pass create the syminfo records for symbols in the library. // 
  @(addnodup, tomod2desc, empty:set.mod2desc, modules.l)

function tomod2desc(m:moddesc)mod2desc 
 setSymbols(src.m, 1, mytype((if length(src(m)_1)> 2 then"T"else"")+ src(m)_1_2), empty:set.syminfo, empty:set.syminfo, uses.m, empty:seq.libtype, empty:seq.seq.word)

function typeastext(t:tree.word)seq.word 
 if nosons.t = 0 then [ label.t]else [ label.t]+"."+ typeastext(t_1)

function setSymbols(md:seq.seq.word, i:int, modname:mytype, defines:set.syminfo, exports:set.syminfo, uses:seq.mytype, typedefs:seq.libtype, tocompile:seq.seq.word)mod2desc 
 if i > length.md 
  then mod2desc(modname, exports, uses, typedefs, defines, tocompile, true)
  else if length(md_i)= 0 
  then setSymbols(md, i + 1, modname, defines, exports, uses, typedefs, tocompile)
  else if md_i_1 ="type"_1 
  then let type = if isabstract.modname 
    then tree(abstracttype.modname, [ tree("T"_1)])
    else tree.abstracttype.modname 
   let pt = parse(md_i, type)
   if label.pt in"encoding Encoding"
   then let asfunc ="function"+ label(pt_1)+"erecord."+ typeastext(pt_2)+ if label.pt in"Encoding"
     then"builtin.NOINLINE.PRECORD"
     else"builtin.NOINLINE.ERECORD"
    let pre = parsesyminfo(modname, asfunc)
    setSymbols(md, i + 1, modname, addnodup(defines, pre), exports, uses, typedefs, tocompile + asfunc)
   else setSymbols(md, i + 1, modname, defines, exports, uses, typedefs + tolibtype2.pt, tocompile)
  else if md_i_1 in"Function function"
  then let pre = parsesyminfo(modname, md_i)
   if subseq(instruction.pre, 1, 1)in ["EXPORT"]
   then setSymbols(md, i + 1, modname, defines, addnodup(exports, pre)+ pre, uses, typedefs, tocompile)
   else if subseq(instruction.pre, 1, 1)in ["UNBOUND"]
   then setSymbols(md, i + 1, modname, addnodup(defines, pre), exports, uses, typedefs, tocompile)
   else let newtocompile = if subseq(instruction.pre, 1, 1)in ["BUILDSEQ","USECALL","ERECORD"]
    then tocompile + md_i 
    else tocompile 
   setSymbols(md, i + 1, modname, addnodup(defines, pre), if md_i_1 ="Function"_1 then exports + pre else exports, uses, typedefs, newtocompile)
  else setSymbols(md, i + 1, modname, defines, exports, uses, typedefs, tocompile)

Function mergelocals(alltypes:set.libtype, m:mod2desc)mod2desc 
 let locals = asset.@(+, locals(alltypes, modname.m), empty:seq.syminfo, typedefs.m)
  mod2desc(modname.m, export.m, uses.m, typedefs.m, locals ∪ defines.m, tocompile.m, isprivate.m)

function addnodup(s:set.syminfo, b:syminfo)set.syminfo 
 let t = findelement2(s, b)
  assert cardinality.t = 0 report"ERROR:duplicate symbol"+ print.b + print(toseq(t)_1)
  s + b

Function linkexports(all:set.mod2desc, s:seq.mod2desc)seq.mod2desc 
 // make sure all exports have equivalent syminfo as defining symbol.Will generate error if cannot find definition to match export // 
  @(+, linkexports.all, empty:seq.mod2desc, s)

function linkexports(mods:set.mod2desc, m:mod2desc)mod2desc 
 let a = @(∪, helper(true, defines.m), empty:set.syminfo, toseq.export.m)
  let b = if cardinality.a = cardinality.export.m 
   then a 
   else let expanded = @(+, expanddefs.mods, empty:seq.syminfo, uses.m)
   @(∪, helper(false, asset.expanded ∪ defines.m), empty:set.syminfo, toseq.export.m)
  // assert not(modname.m = mytype."stdlib")report @(lines, printfull,"", b + defines.m)// 
  mod2desc(modname.m, b, uses.m, typedefs.m, defines.m, tocompile.m, isprivate.m)

function filteroutunbound(s:syminfo)seq.syminfo 
 if subseq(instruction.s, 1, 1)="UNBOUND"then empty:seq.syminfo else [ s]

function helper(firsttime:boolean, all:set.syminfo, s:syminfo)set.syminfo 
 let t = findelement2(all, s)
  let t2 = @(+, filteroutunbound, empty:seq.syminfo, toseq.t)
  assert length.t2 = 1 ∨ firsttime report"ERROR:cannot find symbol for export"+ print.s 
  assert firsttime ∨ length.t2 = 1 ∧ returntype.s = returntype(t2_1)report"ERROR:return type of export does not match definition"+ print.s 
  asset.t2

function expanddefs(mods:set.mod2desc, use:mytype)seq.syminfo 
 let m = findtemplate(mods, use)
  if length.towords.modname.m = 1 
  then toseq.defines.m 
  else @(+, replaceTsyminfo.parameter.use, empty:seq.syminfo, toseq.defines.m)

Function expandexports(mods:set.mod2desc, use:mytype)set.syminfo 
 let m = findtemplate(mods, use)
  if length.towords.modname.m = 1 
  then export.m 
  else @(+, replaceTsyminfo.parameter.use, empty:set.syminfo, toseq.export.m)

Function findtemplate(prim:set.mod2desc, m:mytype)mod2desc 
 let tname = if not.isinstance.m then m else mytype("T"+ abstracttype.m)
  let e = mod2desc(tname, empty:set.syminfo, empty:seq.mytype, empty:seq.libtype, empty:set.syminfo, empty:seq.seq.word, false)
  let x = findelement(e, prim)
  assert not.isempty.x report"ERROR:module"+ print.tname +"NOT FOUND"+ print.m 
  x_1

Function allsymbols(prim:set.mod2desc)set.syminfo 
 let alluses = toseq.asset(@(+, modname, empty:seq.mytype, toseq.prim)+ @(+, uses, empty:seq.mytype, toseq.prim))
  @(∪, xxx2.prim, empty:set.syminfo, alluses)

function xxx2(prim:set.mod2desc, modname:mytype)set.syminfo 
 let t = findtemplate(prim, modname)
  if not.isabstract.modname.t 
  then defines.t 
  else let b = @(+, filteroutunbound, empty:seq.syminfo, toseq.defines.t)
  if parameter.modname = mytype."T"
  then asset.b 
  else @(+, replaceTsyminfo.parameter.modname, empty:set.syminfo, b)

-----------

Function checktypes(alltypes:set.libtype, m:mod2desc)int 
 @(+, checktypes.alltypes, 0, toseq.export.m)+ @(+, checktypes.alltypes, 0, toseq.defines.m)

function checktypes(alltypes:set.libtype, s:syminfo)int 
 let discard = lookuptypes(print.s, alltypes, s)
  0

