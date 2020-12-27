Module format

use set.int

use standard

use seq.seq.word

use stack.seq.word

use stack.word

Function search(pattern:seq.word, s:seq.word, i:int)int
 if i > length.s then i
 else if subseq(s, i, i + length.pattern - 1) = pattern then i
 else search(pattern, s, i + 1)

Function consumecomment(s:seq.word, i:int)int
 // result will be pointer to last word of comment //
 if i > length.s then i
 else if s_i = "//"_1 ∧ not(s_i = "/"_1)then
 consumecomment(s, findindex("//"_1, s, i + 1) + 1)
 else if s_i = "/"_1 ∧ i < length.s
 ∧ s_(i + 1) = "/"_1 then
 consumecomment(s, search("/ /", s, i + 2) + 2)
 else i

Function getheader(s:seq.word)seq.word
 if length.s < 3 then s
 else
  let endofname = if s_3 = ":"_1 then consumetype(s, 5)else 3
   if subseq(s, 1, 3) = "Export type:"then
   let tt = subseq(s, 4, endofname - 1)
     subseq(s, 1, endofname - 1) + "(" + tt + ")" + tt
     + "stub"
   else
    let startoftype = if s_endofname = "("_1 then findindex(")"_1, s, endofname + 1) + 1
    else endofname
    let afterreturntype = consumetype(s, startoftype + 1)
    let aftercomments = consumecomment(s, afterreturntype)
     if aftercomments ≤ length.s ∧ s_aftercomments ∈ "unbound export"then s
     else subseq(s, 1, aftercomments - 1) + "stub"

function consumetype(s:seq.word, i:int)int
 if i > length.s then i
 else if s_i = "."_1 then consumetype(s, i + 2)else i



function match(s:seq.word, depth:int, i:int)int
 if i > length.s then i
 else if s_i = " &{"_1 then match(s, depth + 1, i + 1)
 else if s_i = " &}"_1 then
 if depth = 0 then i else match(s, depth - 1, i + 1)
 else match(s, depth, i + 1)


function escapeformat(length:int, c:word)word
 if c ∈ " &{  &br  &p  &row"then
 if length > 20 then merge.[ encodeword.[ char.10], c]else merge.[ space, c]
 else if c ∈ " &keyword  &}  &em  &strong  &cell"then merge.[ space, c]else c

Function escapeformat(s:seq.word)seq.word s @ +("", escapeformat(length.s, @e))

Function processtotext(x:seq.word)seq.word processtotext(x, 1,"", empty:stack.word)

function needsLF(x:seq.word, i:int)boolean
 // adds LF only if no LF is present //
 if i = 0 then false
 else if x_i = space then needsLF(x, i - 1)
 else if x_i = " &br"_1 then false else true

function processtotext(a:seq.word, i:int, result:seq.word, stk:stack.word)seq.word
 if i > length.a then result
 else
  // assert i < 249 report"KL"+ toword.i + subseq(a, i, i + 3)//
  let this = a_i
  let next = if i < length.a then a_(i + 1)else space
   if this = " &br"_1 then
   if next = " &br"_1 then processtotext(a, i + 1, result, stk)
    else processtotext(a, i + 1, result + " &br" + toseq.stk, stk)
   else if this = " &{"_1 then
   if next = "block"_1 then
    // assert a_(i-1)in"word else w"report"
&{ noformat"+ escapeformat.subseq(a, i-2, i + 3)+" &}"+ result_(length.result-1)+"KL"//
     if // i + 2 &le length.a &and a_(i + 2)≠"
&br"_1 ∧ //
     needsLF(result, length.result)then
     processtotext(a, i + 2, result + " &br" + toseq.stk + space, push(stk, space))
     else processtotext(a, i + 2, result, push(stk, space))
    else if next = "noformat"_1 then
    let t = match(a, 0, i + 2)
      processtotext(a, t + 1, result + subseq(a, i + 2, t - 1), stk)
    else processtotext(a, i + 2, result, push(stk, space))
   else if not.isempty.stk ∧ this = " &}"_1 then
   processtotext(a, i + 1, result + if top.stk = "endtable"_1 then")]"else"", pop.stk)
   else if this = " &keyword"_1 then processtotext(a, i + 2, result + [ next], stk)
   else if this = " &em"_1 then processtotext(a, i + 2, result + [ next], stk)
   else if this = " &p"_1 then processtotext(a, i + 1, result + " &br  &br", stk)
   else processtotext(a, i + 1, result + [ a_i], stk)

Function htmlheader seq.word // the format of the meta tag is carefully crafted to get math unicode characters to display correctly //
"<meta" + merge.' http-equiv ="Content-Type"' + ' content ="text/html; '
+ merge."charset = utf-8"
+ '"> <style type ="text/css"> <!--span.avoidwrap { display:inline-block ; } '
+ ' span.keyword { color:blue ; } span.keywords { color:blue ; } '
+ ' span.literal { color:red ; } span.comment { color:green ; } '
+ ' span.block { padding:0px 0px 0px 0px ; margin:0px 0px 0px 20px ; display:block ; } '
+ ' form{margin:0px ; } html, body { margin:0 ; padding:0 ; height:100% ; }.container { margin:0 ; padding:0 ; height:100% ; display:-webkit-flex ; display:flex ; flex-direction:column ; }.floating-menu { margin:0 ; padding:0 ; background:yellowgreen ; padding:0.5em ; }.content { margin:0 ; padding:0.5em ;-webkit-flex:1 1 auto ; flex:1 1 auto ; overflow:auto ; height:0 ; min-height:0 ; }--> </style> '
+ EOL

Function prettynoparse(s:seq.word)seq.word // format function without first parsing it // prettynoparse(s, 1, 0,"")

function prettynoparse(s:seq.word, i:int, lastbreak:int, result:seq.word)seq.word
 if i > length.s then result
 else
  let x = s_i
   if x = '"'_1 then
   let t = findindex('"'_1, s, i + 1)
     prettynoparse(s, t + 1, lastbreak + t - i, result + " &{ literal" + subseq(s, i, t) + " &}")
   else if x ∈ "// /"then
   let t = consumecomment(s, i)
     if t > i then
     prettynoparse(s, t, t - i, result + " &br  &{ comment" + subseq(s, i, t - 1) + " &}")
     else prettynoparse(s, i + 1, lastbreak + 1, result + x)
   else if x ∈ "if then else let assert function Function type"then
   let t = if lastbreak > 0 then result + " &br"else result
     prettynoparse(s, i + 1, 0, t + " &keyword" + x)
   else if x ∈ "report"then
   prettynoparse(s, i + 1, lastbreak + 1, result + " &keyword" + x)
   else if lastbreak > 20 ∧ x ∈ ")]"
   ∨ lastbreak > 40 ∧ x ∈ ","then
   prettynoparse(s, i + 1, 0, result + x + " &br")
   else if lastbreak > 20 ∧ x ∈ "["then
   prettynoparse(s, i + 1, 0, result + " &br" + x)
   else prettynoparse(s, i + 1, lastbreak + 1, result + x)
   
   
_____________________________

Function  createhtmlfile(name:seq.word,output:seq.word ) int
   createfile("stdout", a.processpara (htmlheader @ addspace(emptyout23,@e), output   ))
 
use outstream.out23

use UTF8

use fileio

use seq.byte    
 
 use bits
 
 use bitpackedseq.byte
 
  type   out23 is record nospace:boolean,a:bitpackedseq.byte
 
    function  +(z:out23,c:char) out23 
  //  clears nospace flag //
   out23(false, if toint.c > 255 then 
       toseqbyte.encodeUTF8.c @ add(a.z,  @e) 
   else   
       add(a.z,byte.toint.c))
       
   function setnospace(   a:out23 ) out23  out23(true,a.a)

builtin createfile2(byteLength:int,data:seq.bits,cstr) int  

 
 function emptyout23 out23 out23(false,empty:bitpackedseq.byte )

