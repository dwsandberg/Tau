Module format


use set.int

use stack.seq.word

use stack.word

use stdlib

Function processpara(t:seq.word)seq.word 
 processpara(t, 1, 1,"", push(empty:stack.seq.word,""))

function processpara(a:seq.word, j:int, i:int, result:seq.word, stk:stack.seq.word)seq.word 
 if i > length.a 
  then result 
  else let this = a_i 
  if not.isempty.stk ∧ top.stk ="&quot"
  then // handle escaping in literals // 
   if this ="&quot"_1 
   then processpara(a, j, i + 1, result +"&quot", pop.stk)
   else processpara(a, j, i + 1, result + addamp.this, stk)
  else if this ="&}"_1 ∧ not.isempty.stk 
  then processpara(a, j, i + 1, result + top.stk + space, pop.stk)
  else if subseq(a, i, i + 1)="&{ error"
  then let end = findindex("&}"_1, a, i + 2)
   processpara(a, j, end + 1, result + subseq(a, i + 2, end - 1), stk)
  else if this ="&keyword"_1 
  then processpara(a, j, i + 2, result +"<span class = keyword>"+ subseq(a, i + 1, i + 1)+"</span>", stk)
  else if this ="&em"_1 
  then processpara(a, j, i + 2, result +"<em>"+ subseq(a, i + 1, i + 1)+"</em>", stk)
  else if this ="&strong"_1 
  then processpara(a, j, i + 2, result +"<strong>"+ subseq(a, i + 1, i + 1)+"</strong>", stk)
  else if this ="&row"_1 
  then if not.isempty.stk ∧ top.stk ="</caption>"
   then processpara(a, j + 1, i + 1, result + EOL +"</caption> <tr id = &quot"+ toword.j +"&quot onclick = &quot cmd5(this)&quot ><td>", pop.stk)
   else processpara(a, j + 1, i + 1, result + EOL +"<tr id = &quot"+ toword.j +"&quot onclick = &quot cmd5(this)&quot ><td>", stk)
  else if this ="&cell"_1 
  then processpara(a, j, i + 1, result + EOL +"<td>", stk)
  else if not.isempty.stk ∧ top.stk ="</span>"∧ this ="&quot"_1 
  then processpara(a, j, i + 1, result +"&quot", push(stk,"&quot"))
  else if this ="&br"_1 
  then if subseq(a, i + 1, i + 2)="&{ block"∨ i > 1 ∧ subseq(a, i - 1, i - 1)="&}"
   then processpara(a, j, i + 1, result, stk)
   else processpara(a, j, i + 1, result + EOL +"<br>"+ space, stk)
  else if this ="&{"_1 ∧ i + 2 < length.a 
  then let next = a_(i + 1)
   if next ="block"_1 
   then processpara(a, j, i + 2, result +"<span class = block>"+ space, push(stk,"</span>"))
   else if next ="keyword"_1 
   then processpara(a, j, i + 2, result +"<span class = keywords>"+ space, push(stk,"</span>"))
   else if next ="noformat"_1 
   then let t = findindex("&}"_1, a, i + 2)
    processpara(a, j, t + 1, result + subseq(a, i + 2, t - 1), stk)
   else if next ="select"_1 
   then if i + 4 < length.a ∧ a_(i + 3)="&section"_1 
    then processpara(a, j, i + 4, result + EOL +"<h2 id ="+ a_(i + 2)+"onclick = &quot javascript:cmd5(this)&quot >"+ space, push(stk,"</h2>"))
    else processpara(a, j, i + 3, result + EOL +"<p id ="+ a_(i + 2)+"onclick = &quot javascript:cmd5(this)&quot >"+ space, push(stk,"</p>"))
   else if next ="table"_1 
   then processpara(a, j, i + 2, result +"<table>"+ space +"<caption>", push(push(stk,"</table>"),"</caption>"))
   else processpara(a, j, i + 2, result +"<span class ="+ next +">", push(stk,"</span>"))
  else if this = space 
  then processpara(a, j, i + 1, result + space, stk)
  else processpara(a, j, i + 1, result + addamp.this, stk)

Function processtotext(x:seq.word)seq.word processtotext(x, 1,"", empty:stack.word)

function processtotext(a:seq.word, i:int, result:seq.word, stk:stack.word)seq.word 
 if i > length.a 
  then result 
  else if a_i ="&quot"_1 
  then let j = findindex("&quot"_1, a, i + 1)
   processtotext(a, j + 1, result + subseq(a, i, j), stk)
  else if a_i ="&br"_1 
  then if a_(i + 1)="&br"_1 
   then processtotext(a, i + 1, result, stk)
   else processtotext(a, i + 1, result + [ EOL]+ toseq.stk, stk)
  else if a_i ="&{"_1 
  then if a_(i + 1)="block"_1 
   then processtotext(a, i + 2, result, push(stk, space))
   else processtotext(a, i + 2, result, push(stk, top.stk))
  else if a_i ="&}"_1 
  then processtotext(a, i + 1, result + if top.stk ="endtable"_1 then")]"else"", pop.stk)
  else if a_i ="&keyword"_1 
  then processtotext(a, i + 2, result + [ a_(i + 1)], stk)
  else if a_i ="&em"_1 
  then processtotext(a, i + 2, result + [ a_(i + 1)], stk)
  else if a_i ="&p"_1 
  then processtotext(a, i + 1, result + [ EOL, EOL], stk)
  else processtotext(a, i + 1, result + [ a_i], stk)

Function htmlheader seq.word 
 {"<meta charset = &quot UTF-8 &quot > <style type = &quot text/css &quot > <!--span.avoidwrap { display:inline-block ; } span.keyword { color:blue ; } span.keywords { color:blue ; } span.literal { color:red ; } span.comment { color:green ; } span.block { padding:0px 0px 0px 0px ; margin:0px 0px 0px 20px ; display:block ; } form{margin:0px ; } html, body { margin:0 ; padding:0 ; height:100% ; }.container { margin:0 ; padding:0 ; height:100% ; display:-webkit-flex ; display:flex ; flex-direction:column ; }.floating-menu { margin:0 ; padding:0 ; background:yellowgreen ; padding:0.5em ; }.content { margin:0 ; padding:0.5em ;-webkit-flex:1 1 auto ; flex:1 1 auto ; overflow:auto ; height:0 ; min-height:0 ; }--> </style>"+ EOL }

Function addamp(w:word)word encodeword.@(+, addamp, empty:seq.int, decode.w)

Function addamp(ch:int)seq.int 
 if ch = 60 
  then  decode."&lt;"_1
  else if ch = 38 then  decode."&amp;"_1 else [ ch]


