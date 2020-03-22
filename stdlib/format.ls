Module format

use set.int

use stdlib

use seq.seq.word

use stack.seq.word

use stack.word

Function EOL word encodeword.[ char.10]

Function processpara(t:seq.word)seq.word processpara(t, 1, 1,"", push(empty:stack.seq.word,""))

function processpara(a:seq.word, j:int, i:int, result:seq.word, stk:stack.seq.word)seq.word
 if i > length.a then result
 else
  let this = a_i
   // if not.isempty.stk ∧ top.stk = '"' then if this = '"'_1 then processpara(a, j, i + 1, result + '"', pop.stk)else processpara(a, j, i + 1, result + addamp.this, stk)else //
   if this = " &}"_1 ∧ not.isempty.stk then
   processpara(a, j, i + 1, result + top.stk + space, pop.stk)
   else
    // if subseq(a, i, i + 1)="
&{ error"then let end = findindex(" &}"_1, a, i + 2)processpara(a, j, end + 1, result + subseq(a, i + 2, end - 1), stk)else //
    if this = " &keyword"_1 then
    processpara(a, j, i + 2, result + "<span class = keyword>" + subseq(a, i + 1, i + 1) + "</span>", stk)
    else if this = " &p"_1 then processpara(a, j, i + 1, result + "<p>", stk)
    else if this = " &em"_1 then
    processpara(a, j, i + 2, result + "<em>" + subseq(a, i + 1, i + 1) + "</em>", stk)
    else if this = " &strong"_1 then
    processpara(a, j, i + 2, result + "<strong>" + subseq(a, i + 1, i + 1) + "</strong>", stk)
    else if this = " &row"_1 then
    if not.isempty.stk ∧ top.stk = "</caption>"then
     processpara(a, j + 1, i + 1, result + EOL + ' </caption> <tr id ="' + toword.j
      + '"onclick ="cmd5(this)"><td> ', pop.stk)
     else
      processpara(a, j + 1, i + 1, result + EOL + ' <tr id ="' + toword.j
      + '"onclick ="cmd5(this)"><td> ', stk)
    else if this = " &cell"_1 then
    processpara(a, j, i + 1, result + EOL + "<td>", stk)
    else
     // if not.isempty.stk ∧ top.stk ="</span>"∧ this = '"'_1 then processpara(a, j, i + 1, result + '"', push(stk, '"'))else //
     if this = " &br"_1 then
     if subseq(a, i + 1, i + 2) = " &{ block"
      ∨ i > 1 ∧ subseq(a, i - 1, i - 1) = " &}"then
      processpara(a, j, i + 1, result, stk)
      else processpara(a, j, i + 1, result + EOL + "<br>" + space, stk)
     else if this = " &{"_1 ∧ i + 2 < length.a then
     let next = a_(i + 1)
       if next = "block"_1 then
       processpara(a, j, i + 2, result + "<span class = block>" + space, push(stk,"</span>"))
       else if next = "keyword"_1 then
       processpara(a, j, i + 2, result + "<span class = keywords>" + space, push(stk,"</span>"))
       else if next = "noformat"_1 then
       let t = // findindex(" &}"_1, a, i + 2)// match(a, 0, i + 2)
         processpara(a, j, t + 1, result + subseq(a, i + 2, t - 1), stk)
       else if next = "select"_1 then
       if i + 4 < length.a ∧ a_(i + 3) = "&section"_1 then
        processpara(a, j, i + 4, result + EOL + "<h2 id =" + a_(i + 2)
         + ' onclick ="javascript:cmd5(this)"> '
         + space, push(stk,"</h2>"))
        else
         processpara(a, j, i + 3, result + EOL + "<p id =" + a_(i + 2)
         + ' onclick ="javascript:cmd5(this)"> '
         + space, push(stk,"</p>"))
       else if next = "table"_1 then
       processpara(a, j, i + 2, result + "<table>" + space + "<caption>", push(push(stk,"</table>"),"</caption>"))
       else
        processpara(a, j, i + 2, result + "<span class =" + next + ">", push(stk,"</span>"))
     else if this = space then processpara(a, j, i + 1, result + space, stk)
     else processpara(a, j, i + 1, result + addamp.this, stk)

function escapeformat(length:int, c:word)word
 if c in " &{  &br  &p  &row"then
 if length > 20 then merge.[ encodeword.[ char.10], c]else merge.[ space, c]
 else if c in " &keyword  &}  &em  &strong  &cell"then merge.[ space, c]else c

Function escapeformat(s:seq.word)seq.word @(+, escapeformat.length.s,"", s)

function match(s:seq.word, depth:int, i:int)int
 if i > length.s then i
 else if s_i = " &{"_1 then match(s, depth + 1, i + 1)
 else if s_i = " &}"_1 then
 if depth = 0 then i else match(s, depth - 1, i + 1)
 else match(s, depth, i + 1)

Function processtotext(x:seq.word)seq.word processtotext(x, 1,"", empty:stack.word)

function needsEOL(x:seq.word, i:int)boolean
 // adds EOL only if no EOL is present //
 if i = 0 then false
 else if x_i = space then needsEOL(x, i - 1)
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
    // assert a_(i - 1)in"word else w"report"
&{ noformat"+ escapeformat.subseq(a, i - 2, i + 3)+" &}"+ result_(length.result - 1)+"KL"//
     if // i + 2 &le length.a &and a_(i + 2)≠"
&br"_1 ∧ //
     needsEOL(result, length.result)then
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

Function htmlheader seq.word // the format of the meta tag is carefully crafted to get math unicode characters to display correctly //"<meta"
+ merge.' http - equiv ="Content - Type"'
+ ' content ="text/html; '
+ merge."charset = utf -8"
+ '"> <style type ="text/css"> <! - - span.avoidwrap { display:inline - block ; } '
+ ' span.keyword { color:blue ; } span.keywords { color:blue ; } '
+ ' span.literal { color:red ; } span.comment { color:green ; } '
+ ' span.block { padding:0px 0px 0px 0px ; margin:0px 0px 0px 20px ; display:block ; } '
+ ' form{margin:0px ; } html, body { margin:0 ; padding:0 ; height:100% ; }.container { margin:0 ; padding:0 ; height:100% ; display:- webkit - flex ; display:flex ; flex - direction:column ; }.floating - menu { margin:0 ; padding:0 ; background:yellowgreen ; padding:0.5em ; }.content { margin:0 ; padding:0.5em ; - webkit - flex:1 1 auto ; flex:1 1 auto ; overflow:auto ; height:0 ; min - height:0 ; } - - > </style> '
+ EOL

Function addamp(w:word)word encodeword.@(+, addamp, empty:seq.char, decodeword.w)

Function addamp(ch:char)seq.char
 if ch = char1."<"then decodeword."&lt;"_1
 else if ch = char1."&"then decodeword."&amp;"_1 else [ ch]

Function prettynoparse(s:seq.word)seq.word // format function without first parsing it // prettynoparse(s, 1, 0,"")

function prettynoparse(s:seq.word, i:int, lastbreak:int, result:seq.word)seq.word
 if i > length.s then result
 else
  let x = s_i
   if x = '"'_1 then
   let t = findindex('"'_1, s, i + 1)
     prettynoparse(s, t + 1, lastbreak + t - i, result + " &{ literal" + subseq(s, i, t) + " &}")
   else if x = "//"_1 then
   let t = findindex("//"_1, s, i + 1)
     prettynoparse(s, t + 1, t - i, result + " &br  &{ comment" + subseq(s, i, t) + " &}")
   else if x in "if then else let assert function Function type"then
   let t = if lastbreak > 0 then result + " &br"else result
     prettynoparse(s, i + 1, 0, t + " &keyword" + x)
   else if x in "report"then
   prettynoparse(s, i + 1, lastbreak + 1, result + " &keyword" + x)
   else if lastbreak > 20 ∧ x in ")]"
   ∨ lastbreak > 40 ∧ x in ","then
   prettynoparse(s, i + 1, 0, result + x + " &br")
   else if lastbreak > 20 ∧ x in "["then
   prettynoparse(s, i + 1, 0, result + " &br" + x)
   else prettynoparse(s, i + 1, lastbreak + 1, result + x)