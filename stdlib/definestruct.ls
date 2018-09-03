module definestruct

use display

use libdesc

use libscope

use passcommon

use seq.mytype

use seq.syminfo

use seq.tree.word

use seq.word

use stdlib

use tree.word

use processtypes

function lastson(s:tree.word)tree.word s_nosons.s

function mytypec(t:tree.word)seq.word 
 if nosons.t = 0 then [ label.t]else mytypec(t_1)+ [ label.t]

Function mytypex(t:tree.word)mytype mytype.mytypec.t

Function functionbody(p:tree.word)tree.word p_2

Function tolibtype2(s:tree.word)libtype 
 let kind = label.s 
  let type = s_1 
  let flds = @(+, lastson, empty:seq.tree.word, subseq(sons.s, 2, nosons.s))
  libtype(label.type, nosons.type = 1, kind, @(+, mytypex, empty:seq.mytype, flds), 
  if kind in"sequence type"then offset.1 else offset.0, @(+, label,"", subseq(sons.s, 2, nosons.s)))

Function locals(sizes:set.libtype, modname:mytype, libtyp:libtype)seq.syminfo 
 // locals returns list of symbols needed to create and access components of structure // 
  let typ = fortype.libtyp 
  let fldtypes = subtypes.libtyp 
  let fldnames = fldnames.libtyp 
  let kind = kind.libtyp 
  if length.fldtypes = 0 
  then empty:seq.syminfo 
  else if length.fldtypes = 1 
  then [ syminfo(fldnames_1, modname, [ typ], fldtypes_1,""), 
  syminfo(abstracttype.typ, modname, [ fldtypes_1], typ,"")]
  else if kind ="struct"_1 
  then [ syminfo(abstracttype.typ, modname, fldtypes, typ,(if sizeoftype(sizes, typ)= offset.length.fldtypes 
   then"RECORD"
   else"BUILD")+ toword.length.fldtypes)]+ fldaccess(sizes, modname, typ, fldtypes, fldnames, offset.0, 1)
  else // assert name.libtyp in"seq pseq dseq cseq arithmeticseq blockseq seq fastsubseq packedseq"report print.libtyp // 
   [ syminfo(abstracttype.typ, modname, fldtypes, typ,"BUILDSEQ"+ toword.length.fldtypes + name.libtyp)]+ @(+, accessfld(modname, typ, fldtypes, fldnames), empty:seq.syminfo, arithseq(length.fldtypes, 1, 1))+ [ syminfo("toseq"_1, modname, [ typ], mytype(towords.parameter.typ +"seq"_1),"")]

function accessfld(modname:mytype, type:mytype, fldtypes:seq.mytype, fldnames:seq.word, i:int)syminfo 
 syminfo(fldnames_i, modname, [ type], fldtypes_i,"LIT"+ toword.i +"IDXUC 2")

function fldaccess(sizes:set.libtype, modname:mytype, type:mytype, fldtypes:seq.mytype, fldnames:seq.word, offset:offset, i:int)seq.syminfo 
 if i > length.fldtypes 
  then empty:seq.syminfo 
  else let sz = sizeoftype(sizes, fldtypes_i)
  fldaccess(sizes, modname, type, fldtypes, fldnames, offset + sz, i + 1)+ syminfo(fldnames_i, modname, [ type], fldtypes_i,"LIT"+ print.offset +"FLD"+ print.sz)

Function parsesyminfo(modname:mytype, text:seq.word)syminfo 
 // parse funcheader to obtain syminfo // 
  let t = parsefuncheader.text 
  let p = t_1 
  let functionname = label.p 
  let functionreturn = lastson.p 
  let paras = subseq(sons.p, 1, nosons.p - 1)
  let funcname = if length.paras = 0 ∧ isabstract.modname 
   then merge([ functionname]+":"+ print.functionreturn)
   else functionname 
  let inst = if label.functionbody.t ="export"_1 
   then"EXPORT"+ toword.length.paras 
   else if label.functionbody.t ="unbound"_1 
   then"UNBOUND"+ toword.length.paras 
   else if label.functionbody.t ="builtin"_1
   then 
   assert nosons.functionbody.t = 1 report "builtin must have one argument:"+ text
      let first= label(functionbody(t)_1)
        // assert  nosons(functionbody(t)_1) =0 &or first in "STATE NOINLINE" report text //
     let second=if nosons(functionbody(t)_1) =0 then "" else [label(functionbody(t)_1_1)]
     let arg1 =if first in "STATE NOINLINE" &and nosons(functionbody(t)_1) =1 then 
      second_1 else first
    let r= if arg1 = "EMPTYSEQ"_1 then
        "LIT 0 LIT 0 RECORD 2"
    else if arg1 = "NOOP"_1 then 
       if functionname in "FORCEINLINE NOINLINE TESTOPT PROFILE" then 
          [functionname]+"1" else ""
    else 
       [if arg1 ="usemangle"_1 
      then mangle(funcname, mytype."builtin", @(+, mytype, empty:seq.mytype, paras))
      else arg1]+  toword.length.paras 
      if nosons(functionbody(t)_1)= 1 
      then 
        r+ ( if first in "STATE NOINLINE" then [first] else second) +"1"
      else r 
   else"USECALL"
  syminfo(funcname, if subseq(inst, 1, 1)="UNBOUND"
   then mytype."T unbound"
   else modname, @(+, mytype, empty:seq.mytype, paras), mytype.functionreturn, inst)

Function prettytext(d:seq.word)seq.word 
 // for prettying up error messages // prettytree(defaultcontrol, parse(d, tree("X"_1)))

