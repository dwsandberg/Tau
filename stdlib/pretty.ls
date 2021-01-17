#!/usr/local/bin/tau 

Module pretty

use parsersupport.attribute2

use seq.attribute2

use seq.token.attribute2

use fileio

use format

use groupparagraphs


use seq.seq.prettyresult

use seq.prettyresult

use standard

use otherseq.word

use seq.seq.word

use set.seq.word


Function gettexts(l:seq.word)seq.seq.word
 subseq(l, 2, length.l) @ +(empty:seq.seq.word, gettexts(l_1, @e))

Function gettexts(lib:word, file:word)seq.seq.word
 let file2 = [ merge([ lib] + "/" + [ file] + ".ls")]
 let b = gettext.file2 @ +(empty:seq.seq.word, gettext2.@e)
  b

function gettext2(s:seq.word)seq.seq.word
 if length.s = 0 then empty:seq.seq.word
 else if s_1 ∈ "Function function type use"then [ s]else empty:seq.seq.word

Function htmlcode(libname:seq.word)seq.word
 let p = prettyfile('  &{ noformat <hr id ="T">  &}  &keyword ', getlibrarysrc.libname_1)
 let modules = p @ +("", findmodules.@e)
  " &{ noformat <h1> Source code for Library" + libname + "</h1>  &}"
  + modules @ +("", ref.@e)
  + p @ list(""," &p", @e)

function ref(modname:word)seq.word
 '  &{ noformat <a href ="' + merge.["#"_1, modname] + '"> ' + modname
 + "</a>  &}"

function findmodules(p:seq.word)seq.word
 if subseq(p, 1, 2) ∈ [" &{ noformat"]then [ p_7]else""

____________________________

Function pretty(l:seq.word, targetdir:seq.word)seq.word
 // first item in list is library and others are files with library to pretty //
 subseq(l, 2, length.l) @ +("", pprettyfile(l_1, targetdir_1, @e))
 
function pprettyfile(lib:word, newlibdir:word, file:word) seq.word
  let p=process.prettyfile(lib,newlibdir,file)
  if aborted.p then message.p else result.p

use process.seq.word

function prettyfile(lib:word, newlibdir:word, file:word)seq.word
 let file2 = [ merge([ lib] + "/" + [ file] + ".ls")]
 let b = prettyfile("", gettext.file2) @ list(""," &p", @e)
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
   let tmp = text.(toseq.parse.s)_1
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
    let p = s
     let u = findindex("uses"_1, p)
     let e = findindex("exports"_1, p)
      " &keyword Library" + p_2 + alphasort.subseq(p, 3, u - 1) + " &br  &keyword"
      + subseq(p, u, e - 1)
      + " &br  &keyword exports"
      + alphasort.subseq(p, e + 1, length.p)
    else escapeformat.s
     if length.uses = 0 then prettyfile(modhead, l, i + 1, uses, libbody, result + temp)
     else prettyfile(modhead, l, i + 1, uses, libbody + temp, result)

function formatuse(a:seq.word)seq.word" &keyword" + reverse.a

function sortuse(a:seq.seq.word)seq.seq.word
 alphasort.toseq.asset.a @ +(empty:seq.seq.word, formatuse.@e)

function pretty(b:seq.attribute2)attribute2
 let a = b @ +(empty:seq.prettyresult, toseq.@e)
 let text = a @ +("", text.@e)
  assert true report"preety&{ noformat" + text + " &}"
  + a @ +(empty:seq.int, prec.@e) @ +("", toword.@e)
   attribute2
   .[ if text_1 ∈ "let if else"then
   prettyresult(100, a @ +(0, width.@e),(if text_1 = "if"_1 then""else" &br") + " &keyword" + text)
   else prettyresult(prec.a_1, a @ +(0, width.@e), text)]

function checkpara(e1:attribute2, e2:attribute2)attribute2
 let e3 = if subseq(text.e2, 1, 3) = " &{ block("then
 attribute2
  .[ prettyresult(0, width.e1 + width.e2," &{ block {" + subseq(text.e2, 3, length.text.e2 - 1) + "}  &}")]
 else e2
  pretty.[ e1, e3]

type prettyresult is record prec:int, width:int, text:seq.word

type attribute2 is record toseq:seq.prettyresult

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
 let totwidth = toseq.a @ +(0, width.@e)
  attribute2
  .[ prettyresult(0
  , if totwidth ≥ 30 then 10000 else totwidth
  , if totwidth < 30 then toseq.a @ list("",",", text.@e)
  else if toseq.a @ max(0, width.@e) < 30 * 10 then
  divideseq(toseq.a @ +(empty:seq.seq.word, text.@e), 10)
  else toseq.a @ list(""," &br,", text.@e))]

function divideseq(b:seq.seq.word, n:int)seq.word
 let l =(length.b + n - 1) / n
  arithseq(l, n, 1) @ list(""," &br,", breakup(b, n, @e))

function breakup(b:seq.seq.word, len:int, i:int)seq.word
 subseq(b, i, i + len - 1) @ list("",",", @e)

function left(i:int)int // exp precedence when use on left of operator // if i < 100 then i else 99

function right(i:int)int // exp precedence when use on right of operator // if i < 100 then i else i - 100

function wrap(prec:int, prein:attribute2, binary:seq.word, postin:attribute2)attribute2
 let pre =(toseq.prein)_1
 let post =(toseq.postin)_1
 let x = if width.pre + width.post > 30 then
 " &br" + if binary ∈ [".","_","^"]then binary else binary + space
 else if binary ∈ [".","_","^"]then binary else [ space] + binary + space
 let pre1 = if left.prec.pre > prec then"(" + text.pre + ")"else text.pre
 let a = [ if right.prec.post > prec ∨ prec ≠ 3 ∧ prec = right.prec.post then
 prettyresult(prec, width.pre + width.x + width.post,(pre1 + if binary = "."then"("else x + "(") + text.post
  + ")")
 else
  prettyresult(if prec.post ≥ 100 then prec + 100 else prec, width.pre + width.x + width.post, pre1 + x + text.post)]
  // assert text.pre ="33"report text.pre +"("+ toword.left.prec.pre + toword.prec.pre + binary + toword.right.prec.post + toword.prec.post +")"+ text.post +"result"+ toword.prec.a_1 //
  attribute2.a

function unaryminus(exp:attribute2)attribute2
 let prec = 3
 let post =(toseq.exp)_1
  attribute2
  .[ if right.prec.post > prec then
  prettyresult(prec, 3 + width.post,"-" + "(" + text.post + ")")
  else
   prettyresult(if prec.post ≥ 100 then prec + 100 else prec, 1 + width.post,"-" + text.post)]

function block(b:attribute2)attribute2 block("", b)

function block(keys:seq.word, b:attribute2)attribute2
 let a =(toseq.b)_1
 let txt = text.a
  attribute2
  .[ if length.txt > 3 ∧ txt_3 ∈ keys then a else prettyresult(prec.a, 10000, block.txt)]

function block(txt:seq.word)seq.word
 let txt2 = if txt_1 = " &br"_1 then subseq(txt, 2, length.txt)else txt
  " &{ block" + txt2 + " &}"

function elseblock(a:attribute2)attribute2
 let exp =(toseq.a)_1
  attribute2
  .[ if width.exp < 30 then prettyresult(0, width.exp," &br  &keyword else" + text.exp)
  else
   // assert false report" &{ noformat"+ text.exp +" &}"//
   if subseq(text.exp, 1, 2) = " &keyword if"then
   prettyresult(0, 10000," &br  &keyword else" + text.exp)
   else prettyresult(0, 10000," &br  &keyword else" + block.text.exp)]


function key(a:attribute2)attribute2 attribute(" &keyword" + text.a)

function width(s:seq.word)int length.s

Below is generated from parser generator.

Function action(ruleno:int,  input:seq.word,place:int, R:reduction.attribute2)attribute2 
if ruleno = // G F # // 1 then R_1 
else if ruleno = // F W NM(FP)T E // 2 then pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7] 
else if ruleno = // F W N(FP)T E // 3 then pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7] 
else if ruleno = // F W NM T E // 4 then pretty.[ key.R_1, R_2, R_3, R_4] 
else if ruleno = // F W NM is W P // 5 then pretty.[ key.R_1, R_2, R_3, R_4, list.R_5] 
else if ruleno = // F T // 6 then // use // pretty.[ R_1] 
else if ruleno = // FP P // 7 then list.R_1 
else if ruleno = // P T // 8 then R_1 
else if ruleno = // P P, T // 9 then R_1 + R_3 
else if ruleno = // P W:T // 10 then pretty.[ R_1, R_2, R_3] 
else if ruleno = // P P, W:T // 11 then R_1 + pretty.[ R_3, R_4, R_5] 
else if ruleno = // P comment W:T // 12 then pretty.[ R_1, R_2, R_3, R_4] 
else if ruleno = // P P, comment W:T // 13 then R_1 + pretty.[ R_3, R_4, R_5, R_6] 
else if ruleno = // E NM // 14 then R_1 
else if ruleno = // E NM(L)// 15 then if length.R_3 = 1 ∧ length.text.R_1 = 1 then wrap(3, R_1,".", R_3)else pretty.[ R_1, R_2, list.R_3, R_4] 
else if ruleno = // E(E)// 16 then R_2 
else if ruleno = // E { E } // 17 then R_2 
else if ruleno = // E if E then E else E // 18 then // if width.R_2 + width.R_4 < 30 then pretty.[ R_1, R_2, key.R_3, R_4, elseblock.R_6]else pretty.[ R_1, R_2, attribute2."then", block.R_4, elseblock.R_6]else // if width.R_2 + width.R_4 + width.R_6 < 30 then pretty.[ R_1, R_2, key.R_3, R_4, key.R_5, R_6]else if width.R_2 + width.R_4 < 30 then pretty.[ R_1, R_2, key.R_3, R_4, elseblock.R_6]else pretty.[ R_1, R_2, attribute."&keyword then &br", block.R_4, elseblock.R_6] 
else if ruleno = // E E_E // 19 then wrap(1, R_1, text.R_2, R_3) 
else if ruleno = // E-E // 20 then unaryminus.R_2 
else if ruleno = // E W.E // 21 then wrap(3, R_1, text.R_2, R_3) 
else if ruleno = // E E * E // 22 then wrap(4, R_1, text.R_2, R_3) 
else if ruleno = // E E-E // 23 then wrap(5, R_1, text.R_2, R_3) 
else if ruleno = // E E = E // 24 then wrap(6, R_1, text.R_2, R_3) 
else if ruleno = // E E > E // 25 then wrap(7, R_1, text.R_2, R_3) 
else if ruleno = // E E ∧ E // 26 then wrap(8, R_1, text.R_2, R_3) 
else if ruleno = // E E ∨ E // 27 then wrap(9, R_1, text.R_2, R_3) 
else if ruleno = // L E // 28 then R_1 
else if ruleno = // L L, E // 29 then R_1 + R_3 
else if ruleno = // E [ L]// 30 then pretty.[ R_1, list.R_2, R_3] 
else if ruleno = // A let W = E // 31 then pretty.[ R_1, R_2, R_3, R_4] 
else if ruleno = // E A E // 32 then checkpara(R_1, block("&br let assert", R_2)) 
else if ruleno = // E assert E report E E // 33 then pretty.[ R_1, R_2, key.R_3, R_4, block("&br let assert", R_5)] 
else if ruleno = // E I // 34 then R_1 
else if ruleno = // E I.I // 35 then pretty.[ R_1, R_2, R_3] 
else if ruleno = // T W // 36 then R_1 
else if ruleno = // T W.T // 37 then pretty.[ R_1, R_2, R_3] 
else if ruleno = // E $wordlist // 38 then attribute2([ prettyresult(0, length.text.R_1,"&{ literal"+ escapeformat.text.R_1 +"&}")]) 
else if ruleno = // E comment E // 39 then 
let t ="&{ comment"+ escapeformat.text.R_1 +"&}" 
let t2 = if width.R_1 + width.R_2 > 30 ∧(text.R_2)_1 ≠"&br"_1 then t +"&br"else t pretty.[ attribute2.[ prettyresult(0, length.text.R_1, t2)], R_2] 
else if ruleno = // N_// 40 then R_1 
else if ruleno = // N-// 41 then R_1 
else if ruleno = // N = // 42 then R_1 
else if ruleno = // N > // 43 then R_1 
else if ruleno = // N * // 44 then R_1 
else if ruleno = // N ∧ // 45 then R_1 
else if ruleno = // N ∨ // 46 then R_1 
else if ruleno = // NM W // 47 then R_1 
else if ruleno = // NM W:T // 48 then pretty.[ R_1, R_2, R_3] 
else if ruleno = // D E @ NM(E, // 49 then    
   attribute2( [R_1,  pretty.[R_3, R_4, R_5,R_6] ] @ +(empty:seq.prettyresult, toseq.@e))
else if ruleno = // D E @ N(E, // 50 then  
   attribute2( [R_1,  pretty.[R_3, R_4, R_5,R_6] ] @ +(empty:seq.prettyresult, toseq.@e)) 
else assert ruleno = // E D L)// 51 report"invalid rule number"+ toword.ruleno
     wrap(4,attribute2.[(toseq.R_1)_1],"@", pretty.[ attribute2.[(toseq.R_1)_2], list.R_2 ,R_3]) 
