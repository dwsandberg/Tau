#!/usr/local/bin/tau

Module pretty

use fileio

use format

use groupparagraphs

use standard

use parsersupport.attribute2

use seq.attribute2

use seq.prettyresult

use otherseq.word

use seq.token.attribute2

use seq.seq.prettyresult

use process.seq.word

use seq.seq.word

use set.seq.word

Function gettexts(l:seq.word)seq.seq.word
 for acc = empty:seq.seq.word, @e = subseq(l, 2, length.l)do
  acc + gettexts(l_1, @e)
 end(acc)

Function gettexts(lib:word, file:word)seq.seq.word
let file2 = [ merge([ lib] + "/" + [ file] + ".ls")]
 for acc = empty:seq.seq.word, @e = gettext.file2 do acc + gettext2.@e end(acc)

function gettext2(s:seq.word)seq.seq.word
 if length.s = 0 then empty:seq.seq.word
 else if s_1 ∈ "Function function type use"then [ s]else empty:seq.seq.word

Function htmlcode(libname:seq.word)seq.word
let p = prettyfile('  &{ noformat <hr id ="T">  &}  &keyword ', getlibrarysrc.libname_1)
let modules = for acc ="", @e = p do acc + findmodules.@e end(acc)
 " &{ noformat <h1> Source code for Library" + libname + "</h1>  &}"
 + for acc ="", @e = modules do acc + ref.@e end(acc)
 + for acc ="", @e = p do list(acc," &p", @e)end(acc)

function ref(modname:word)seq.word
 '  &{ noformat <a href ="' + merge.["#"_1, modname] + '"> ' + modname
 + "</a>  &}"

function findmodules(p:seq.word)seq.word
 if subseq(p, 1, 2) ∈ [" &{ noformat"]then [ p_7]else""

____________________________

Function pretty(l:seq.word, targetdir:seq.word)seq.word
 \\ first item in list is library and others are files with library to pretty \\
 for acc ="", @e = subseq(l, 2, length.l)do acc + pprettyfile(l_1, targetdir_1, @e)end(acc)

function pprettyfile(lib:word, newlibdir:word, file:word)seq.word
let p = process.prettyfile(lib, newlibdir, file)
 if aborted.p then message.p else result.p

function prettyfile(lib:word, newlibdir:word, file:word)seq.word
let file2 = [ merge([ lib] + "/" + [ file] + ".ls")]
let b = for acc ="", @e = prettyfile("", gettext.file2)do list(acc," &p", @e)end(acc)
let discard = createfile([ merge([ newlibdir] + "/" + file + ".ls")], processtotext.b)
 b

Function prettyfile(modhead:seq.word, s:seq.seq.word)seq.seq.word
 prettyfile(modhead, s, 1, empty:seq.seq.word, empty:seq.seq.word, empty:seq.seq.word)

function prettyfile(modhead:seq.word, l:seq.seq.word, i:int, uses:seq.seq.word, libbody:seq.seq.word, result:seq.seq.word)seq.seq.word
 if i > length.l then result + sortuse.uses + libbody
 else
  let s = l_i
   if length.s = 0 then prettyfile(modhead, l, i + 1, uses, libbody, result)
   else if s_1 ∈ "use"then prettyfile(modhead, l, i + 1, uses + reverse.s, libbody, result)
   else if s_1 ∈ "Function function type"then
   let tmp0 = text.(toseq.parse.s)_1
   let tmp = removeclose(tmp0, length.tmp0)
   let tmp2 = if s_1 ∈ "Function function" ∧ last.tmp = "export"_1 then
   " &keyword Export" + subseq(tmp, 3, length.tmp - 1)
   else tmp
    prettyfile(modhead, l, i + 1, uses, libbody + tmp2, result)
   else if s_1 ∈ "module Module"then
   let target = if length.modhead > 1 then
   subseq(modhead, 1, 6) + s_2 + subseq(modhead, 8, length.modhead)
   else empty:seq.word
   let newresult = result + sortuse.uses + libbody + (target + s)
    prettyfile(modhead, l, i + 1, empty:seq.seq.word, empty:seq.seq.word, newresult)
   else
    let temp = if s_1 ∈ "Library library"then
    let parts = break(s,"uses exports", true)
     " &keyword Library" + s_2 + alphasort(parts_1 << 2) + " &br  &keyword"
     + parts_2
     + " &br  &keyword exports"
     + alphasort(parts_3 << 1)
    else escapeformat.s
     if length.uses = 0 then prettyfile(modhead, l, i + 1, uses, libbody, result + temp)
     else prettyfile(modhead, l, i + 1, uses, libbody + temp, result)

function formatuse(a:seq.word)seq.word" &keyword" + reverse.a

function sortuse(a:seq.seq.word)seq.seq.word
 for acc = empty:seq.seq.word, @e = alphasort.toseq.asset.a do acc + formatuse.@e end(acc)

function pretty(b:seq.attribute2)attribute2
let a = for acc = empty:seq.prettyresult, @e = b do acc + toseq.@e end(acc)
let text = for acc ="", @e = a do acc + text.@e end(acc)
 attribute2.[ prettyresult(prec.first.a, for acc = 0, @e = a do acc + width.@e end(acc), text)]

\\ for width = 0, text ="", attr = b do next(width + width.first.toseq.attr, text + text.first.toseq.attr)end(attribute2.[ prettyresult(prec.toseq.first.first.toseq.b, width, text)])\\

function protect(a:seq.word, b:seq.word)seq.word
let a1 = lastsymbol(a, length.a)
let b1 = if subseq(b, 1, 3) = " &{ block  &keyword"then b_4
else if subseq(b, 1, 2) = " &{ block"then b_3
else if first.b = " &keyword"_1 then b_2
else if subseq(b, 1, 2) = "block  &keyword"then b_3 else b_1
 if a1 = ";"_1 ∧ b1 ∉ "-+("then
 removeclose(a, length.a) + b
 else if b1 ∈ "-+" ∧ a1 ∉ ";"then
 "(" + a + ")(" + b + ")"
 else if b1 ∈ "(" ∧ a1 ∉ (";)]'" + "'")then
 "(" + a + ")" + b
 else a + b

function removeclose(a:seq.word, i:int)seq.word
 if a_i = " &}"_1 then removeclose(a, i - 1) + " &}"_1
 else if a_i = ";"_1 then removeclose(a, i - 1)else subseq(a, 1, i)

function removeclose(a:seq.word)seq.word if isempty.a then a else removeclose(a, length.a)

function lastsymbol(a:seq.word, i:int)word
 if a_i = " &}"_1 then lastsymbol(a, i - 1)else a_i

type prettyresult is prec:int, width:int, text:seq.word

type attribute2 is toseq:seq.prettyresult

function parse(l:seq.word)attribute2 parse:attribute2(l)

Export type:attribute2

Export type:prettyresult

Function attribute(text:seq.word)attribute2 attribute2.[ prettyresult(0, width.text, text)]

function attribute:attribute2(text:seq.word)attribute2 attribute2.[ prettyresult(0, width.text, text)]

function forward(stk:attribute2, token:attribute2)attribute2 token

function remainingwidth(a:prettyresult)int width.a mod 10000

Function text(a:attribute2)seq.word text.(toseq.a)_1

function width(a:attribute2)int width.(toseq.a)_1

function +(a:attribute2, b:attribute2)attribute2 attribute2(toseq.a + toseq.b)

function length(a:attribute2)int length.toseq.a

function list(a:attribute2)attribute2
let totwidth = for acc = 0, @e = toseq.a do acc + width.@e end(acc)
let noperline = if totwidth < 30 then 10000
else if for acc = 0, @e = toseq.a do max(acc, width.@e)end(acc)
< 30 * 10 then
10
else 1
 attribute2.[ prettyresult(0, if totwidth ≥ 30 then 10000 else totwidth, for acc ="", i = 1, e = toseq.a do
  next(acc + removeclose.text.e + if i = noperline then" &br,"else",", if i = noperline then 1 else i + 1)
 end(acc >> 1))
 ]

function wrap(prec:int, prein:attribute2, binary:seq.word, postin:attribute2)attribute2
let pre =(toseq.prein)_1
let post =(toseq.postin)_1
let x = if width.pre + width.post > 30 ∧ binary ≠ "."then
" &br"
 + if binary ∈ [".","_","^"]then binary else binary + space
else if binary ∈ [".","_","^"]then binary else [ space] + binary + space
let pre1 = if prec.pre > prec then"(" + text.pre + ")"else text.pre
let a = if prec.post > prec ∨ prec ≠ 3 ∧ prec = prec.post then
prettyresult(prec, width.pre + width.x + width.post, pre1 + if binary = "."then"("else x + "(";
 + text.post
 + ")")
else
 \\ assert binary &ne"+"report"wrap"+ print.prec.pre + print.prec.post + print.prec \\
 prettyresult(prec, width.pre + width.x + width.post, pre1 + x + text.post)
 \\ assert text.pre ="33"report text.pre +"("+ toword.left.prec.pre + toword.prec.pre + binary + toword.right.prec.post + toword.prec.post +")"+ text.post +"result"+ toword.prec.a_1 \\
 attribute2.[ a]

function unaryminus(exp:attribute2)attribute2
let prec = 3
let post =(toseq.exp)_1
 attribute2.[ if prec.post > prec then
 prettyresult(prec, 3 + width.post,"-" + "(" + text.post + ")")
 else prettyresult(prec, 1 + width.post,"-" + text.post)]

function block(b:attribute2)attribute2 block("", b)

function block(keys:seq.word, b:attribute2)attribute2
let a =(toseq.b)_1
let txt = text.a
 attribute2.[ if length.txt > 3 ∧ txt_3 ∈ keys then a
 else if length.txt > 2 ∧ txt_2 ∈ "let"then
 prettyresult(prec.a, 10000," &br" + text.a)
 else prettyresult(prec.a, 10000, blocktxt.txt)
 ]

function blocktxt(txt:seq.word)seq.word
 " &{ block" + if txt_1 = " &br"_1 then txt << 1 else txt ;
 + " &}"

function elseblock(a:attribute2)attribute2
let exp =(toseq.a)_1
 attribute2.[ if width.exp < 30 then prettyresult(0, width.exp," &br  &keyword else" + text.exp)
 else
  \\ assert"if"_1 &nin text.exp report"here"+ text.exp \\
  if subseq(text.exp, 1, 2) = " &keyword if"then
  prettyresult(0, 10000," &br  &keyword else" + text.exp)
  else prettyresult(0, 10000," &br  &keyword else" + blocktxt.text.exp)
 ]

function key(a:attribute2)attribute2 attribute(" &keyword" + text.a)

function width(s:seq.word)int length.s

Below is generated from parser generator.

Function action(ruleno:int, input:seq.word, place:int, R:reduction.attribute2)attribute2
if ruleno = \\ G F # \\ 1 then R_1 
else if ruleno = \\ F W NM(FP)T E \\ 2 then pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7] 
else if ruleno = \\ F W_(FP)T E \\ 3 then pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7] 
else if ruleno = \\ F W-(FP)T E \\ 4 then pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7] 
else if ruleno = \\ F W =(FP)T E \\ 5 then pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7] 
else if ruleno = \\ F W >(FP)T E \\ 6 then pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7] 
else if ruleno = \\ F W *(FP)T E \\ 7 then pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7] 
else if ruleno = \\ F W ∧(FP)T E \\ 8 then pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7] 
else if ruleno = \\ F W ∨(FP)T E \\ 9 then pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7] 
else if ruleno = \\ F W NM T E \\ 10 then pretty.[ key.R_1, R_2, R_3, R_4] 
else if ruleno = \\ F W NM is P \\ 11 then pretty.[ key.R_1, R_2, R_3, list.R_4] 
else if ruleno = \\ FP P \\ 12 then list.R_1 
else if ruleno = \\ P T \\ 13 then R_1 
else if ruleno = \\ P P, T \\ 14 then R_1 + R_3 
else if ruleno = \\ P W:T \\ 15 then pretty.[ R_1, R_2, R_3] 
else if ruleno = \\ P P, W:T \\ 16 then R_1 + pretty.[ R_3, R_4, R_5] 
else if ruleno = \\ P comment W:T \\ 17 then pretty.[ R_1, R_2, R_3, R_4] 
else if ruleno = \\ P P, comment W:T \\ 18 then R_1 + pretty.[ R_3, R_4, R_5, R_6] 
else if ruleno = \\ E NM \\ 19 then R_1 
else if ruleno = \\ E NM(L)\\ 20 then if length.R_3 = 1 ∧ length.text.R_1 = 1 then wrap(3, R_1,".", R_3)else pretty.[ R_1, R_2, list.R_3, R_4] 
else if ruleno = \\ E(E)\\ 21 then R_2 
else if ruleno = \\ E if E then E else D \\ 22 then 
let x1 ="&keyword if"+ removeclose.text.R_2 +"&keyword then" 
let x = attribute(x1 + removeclose.text.R_4) 
let t = if width.R_2 + width.R_4 + width.R_6 < 30 then [ x, key.R_5, R_6]else if width.R_2 + width.R_4 < 30 then [ x, elseblock.R_6]else [ attribute(x1 + removeclose.text.block.R_4), elseblock.R_6]pretty(t + attribute.";") 
else if ruleno = \\ E E_E \\ 23 then wrap(1, R_1, text.R_2, R_3) 
else if ruleno = \\ E-E \\ 24 then unaryminus.R_2 
else if ruleno = \\ E W.E \\ 25 then wrap(3, R_1, text.R_2, R_3) 
else if ruleno = \\ E E * E \\ 26 then wrap(4, R_1, text.R_2, R_3) 
else if ruleno = \\ E E-E \\ 27 then wrap(5, R_1, text.R_2, R_3) 
else if ruleno = \\ E E = E \\ 28 then wrap(6, R_1, text.R_2, R_3) 
else if ruleno = \\ E E > E \\ 29 then wrap(7, R_1, text.R_2, R_3) 
else if ruleno = \\ E E ∧ E \\ 30 then wrap(8, R_1, text.R_2, R_3) 
else if ruleno = \\ E E ∨ E \\ 31 then wrap(9, R_1, text.R_2, R_3) 
else if ruleno = \\ L E \\ 32 then R_1 
else if ruleno = \\ L L, E \\ 33 then R_1 + R_3 
else if ruleno = \\ E [ L]\\ 34 then pretty.[ R_1, list.R_2, R_3] 
else if ruleno = \\ A W = E \\ 35 then pretty.[ R_1, R_2, R_3] 
else if ruleno = \\ E let A E \\ 36 then \\ checkpara(pretty.[ R_1, R_2], block("&br 
let 
assert", R_3))\\ attribute("&keyword 
let"+ subseq(text.R_2, 1, 2)+ protect(text.R_2 << 2, text.block("&br 
let 
assert", R_3))) 
else if ruleno = \\ E assert E report D E \\ 37 then pretty.[ key.R_1, R_2, attribute("&keyword report"+ protect(text.R_4, text.block("&br 
let 
assert", R_5)))] 
else if ruleno = \\ E I \\ 38 then R_1 
else if ruleno = \\ E I.I \\ 39 then pretty.[ R_1, R_2, R_3] 
else if ruleno = \\ T W \\ 40 then R_1 
else if ruleno = \\ T W.T \\ 41 then pretty.[ R_1, R_2, R_3] 
else if ruleno = \\ E $wordlist \\ 42 then attribute2.[ prettyresult(0, length.text.R_1,"&{ literal"+ escapeformat.text.R_1 +"&}")] 
else if ruleno = \\ E comment E \\ 43 then 
let t ="&{ comment \\"+ escapeformat.text.R_1 << 1 >> 1 +"\\ &}" 
let t2 = if width.R_1 + width.R_2 > 30 ∧(text.R_2)_1 ≠"&br"_1 then t +"&br"else t pretty.[ attribute2.[ prettyresult(0, length.text.R_1, t2)], R_2] 
else if ruleno = \\ NM W \\ 44 then R_1 
else if ruleno = \\ NM W:T \\ 45 then pretty.[ R_1, R_2, R_3] 
else if ruleno = \\ D E \\ 46 then R_1 
else if ruleno = \\ D E ; \\ 47 then R_1 
else if ruleno = \\ F1 W = E \\ 48 then pretty.[ R_1, R_2, R_3] 
else if ruleno = \\ F1 F1, W = E \\ 49 then pretty.[ R_1, R_2, R_3, R_4, R_5] 
else if ruleno = \\ F2 F1 \\ 50 then R_1 
else if ruleno = \\ E for F2 do E end(E)\\ 51 then if width.R_2 + width.R_4 < 30 then pretty.[ key.R_1, list.R_2, attribute("&keyword do"+ removeclose.text.R_4 +"&keyword end"), R_6, R_7, R_8]else pretty.[ key.R_1, list.R_2, attribute("&keyword do"+ removeclose.text.block.R_4 +"&br &keyword end"), R_6, R_7, R_8] 
else assert ruleno = \\ E for F2 while(E)E end(E)\\ 52 
report"invalid rule number"+ toword.ruleno 
 pretty.[ key.R_1, list.R_2, attribute("&keyword while("+ text.R_5 +")"+ removeclose.text.R_7 +"&keyword end"), R_9, R_10, R_11]
