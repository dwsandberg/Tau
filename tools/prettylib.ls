Module prettylib

use UTF8

use definestruct

use display

use textio

use format

use libdesc

use libscope

use main

use parse

use passcommon

use pretty

use seq.moddesc

use seq.mytype

use seq.ptree

use seq.syminfo

use seq.tree.word

use seq.word

use set.seq.word

use stack.tree.word

use stdlib

use tree.word

use renamemodule

function reverse2(l:seq.word)seq.word 
 if isempty.l then l else reverse2.subseq(l, 2, length.l)+ l_1

Function prettylib(libname:seq.word,namemap:seq.word)seq.word 
 // Pretty prints lib source. Does not create files for modules where the pretty printed version does not give the same parse tree. // 
  // Warning:Discards text before first module. Multiple modules in the same file are broken into multiple files. // 
  // Will move a beginning comment inside parentheses and fail on(a + b)* b. // 
  // namemap is form changing module names in form "oldname1 newname1 oldname2 newname2 ..." //
  let lib = if length.namemap > 0 then maplib(tolibdesc(libname_1),namemap) else tolibdesc(libname_1)
  let libheader = ["#!/usr/local/bin/tau", 
  "Library"+ libname + alphasort.@(+, modname,"", subseq(modules.lib, 2, length.modules.lib))+ EOL +
  "uses"+ dependentlibs.lib + EOL +"exports"+ alphasort.exports.lib]
  assert @(∧, checkpretty.libheader, true, modules.lib)report"failed"
  {"PASSED"}

function checkpretty(libheader:seq.seq.word, mod:moddesc)boolean 
 let x = checkpretty(src(mod), 1, empty:set.seq.word, empty:seq.seq.word, empty:seq.seq.word)
  let z = createfile([ merge([ libname(mod)]+"/"+ [ modname(mod)]+".ls")], if modname(mod)= libname(mod)then libheader + x else x)
  true

function checkpretty(s:seq.seq.word, i:int, use:set.seq.word, before:seq.seq.word, after:seq.seq.word)seq.seq.word 
 if i > length.s 
  then before + alphasort.toseq.use + after 
  else let p = s_i 
  if length.p = 0 
  then checkpretty(s, i + 1, use, before, after)
  else if not(p_1 in"function Function type use")
  then if isempty.use then checkpretty(s, i + 1, use, before + p, after)else checkpretty(s, i + 1, use, before, after + p)
  else let orgtree = parse(p, tree("xxx"_1))
  let formatedtext = processtotext.prettytree(defaultcontrol, orgtree)
  let newtext = towords.toseqint.toUTF8.formatedtext 
  let newtree = parse(newtext, tree("xxx"_1))
  assert newtree = orgtree report"FAILED on"+ formatedtext 
  if p_1 ="use"_1 
  then checkpretty(s, i + 1, use + formatedtext, before, after)
  else if isempty.use 
  then checkpretty(s, i + 1, use, before + formatedtext, after)
  else checkpretty(s, i + 1, use, before, after + formatedtext)

Function checkbind(libname:seq.word)seq.word 
 // Verifies that that same parse tree can be created from the binding form of functions as from source txt. Does not check abstract type functions. // 
  let lib = tolibdesc(libname_1)
  let x = newcode.bindings(libname_1)
  let ptrees = @(+, getparsetrees, empty:seq.ptree, modules.lib)
  let a = @(+, checkbind.ptrees,"", subseq(x, 1, 40000))
  if a =""
  then"PASSED BINDING CHECK for"+ libname 
  else"FAILED BINDING CHECK for"+ libname +". Detail:"+ a

type ptree is record symbol:syminfo, parsetree:tree.word

function getparsetrees(s:moddesc)seq.ptree @(+, getparsetree.modname.s, empty:seq.ptree, src.s)

function getparsetree(modname:word, s:seq.word)seq.ptree 
 if length.s = 0 ∨ not(s_1 in"function Function")
  then empty:seq.ptree 
  else [ ptree(parsesyminfo(mytype.[ modname], s), parse(s, tree("xxx"_1)))]

function checkbind(p:seq.ptree, s:syminfo)seq.word 
 let t = @(+, checkbind.s,"", p)
  if t ="OK"
  then""
  else // if length.t = 0 then"&br"+ [ name.s]+":"+ print.modname.s + instruction.s else // t

function checkbind(sym:syminfo, p:ptree)seq.word 
 // if iscomplex.modname.sym then""else // 
  if name.sym = name.symbol.p ∧ paratypes.sym = paratypes.symbol.p ∧ modname.sym = modname.symbol.p 
  then if label(parsetree(p)_2)in"builtin export"
   then"OK"
   else let b = toparse(instruction.sym, 2, empty:stack.tree.word)
   if b = parsetree(p)_2 
   then"OK"
   else"&br"+ name.sym + print.modname.sym +"&br"+ print.parsetree.p +"&br"+ print.b +"&br"+ instruction.sym 
  else""

function toparse(s:seq.word, i:int, r:stack.tree.word)tree.word 
 if i > length.s 
  then top.r 
  else if s_i in"LIT WORD"
  then toparse(s, i + 2, push(r, tree(s_(i + 1))))
  else let nosons = toint(s_(i + 1))
  let cd = codedown(s_i)
  let name = if length.cd = 2 ∧ length(cd_2)> 1 ∧ length.cd = 2 
   then // assert false report cd_1 +"mod"+ cd_2 + towords.decode.(cd_1_1)// 
    let a = towords.decode(cd_1_1)
    if a_length.a ="T"_1 
    then let z = merge(subseq(a, 1, length.a - 1)+ @(seperator.".", identity,"", reverse2.subseq(cd_2, 1, length(cd_2) - 1)))
     // assert z = merge."empty:seq.word"report [ z, cd_1_1]// z 
    else cd_1_1 
   else cd_1_1 
  let t = tree(name, top(r, nosons))
  toparse(s, i + 2, push(pop(r, nosons), t))

