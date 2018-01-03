Module format

use pretty2

use set.int

use stack.seq.word

use stack.word

use stdlib

Function processpara(t:seq.word)seq.word 
 processpara(t, 1, 1,"", push(empty:stack.seq.word,""))

function processpara(a:seq.word, j:int, i:int, result:seq.word, stk:stack.seq.word)seq.word 
 if i > length.a 
  then result 
  else if top.stk =""""
  then // handle escaping in literals // 
   if a_i =""""_1 
   then processpara(a, j, i + 1, result +"""", pop.stk)
   else processpara(a, j, i + 1, result + addamp(a_i), stk)
  else if a_i ="&}"_1 ∧ not.isempty.stk 
  then processpara(a, j, i + 1, result + top.stk + space, pop.stk)
  else if subseq(a, i, i + 1)="&{ error"
  then let end = findindex("&}"_1, a, i + 2)
   processpara(a, j, end + 1, result + subseq(a, i + 2, end - 1), stk)
  else if i < length.a 
  then if a_i ="&keyword"_1 
   then processpara(a, j, i + 2, result +"<span class = keyword>"+ a_(i + 1)+"</span>", stk)
   else if a_i ="&em"_1 
   then processpara(a, j, i + 2, result +"<em>"+ a_(i + 1)+"</em>", stk)
   else if a_i ="&strong"_1 
   then processpara(a, j, i + 2, result +"<strong>"+ a_(i + 1)+"</strong>", stk)
   else if a_i ="&row"_1 
   then if top.stk ="</caption>"
    then processpara(a, j + 1, i + 1, result + EOL +"</caption> <tr id ="""+ toword.j +"""onclick =""cmd5(this)""><td>", pop.stk)
    else processpara(a, j + 1, i + 1, result + EOL +"<tr id ="""+ toword.j +"""onclick =""cmd5(this)""><td>", stk)
   else if a_i ="&cell"_1 
   then processpara(a, j, i + 1, result + EOL +"<td>", stk)
   else if top.stk ="</span>"∧ a_i =""""_1 
   then processpara(a, j, i + 1, result +"""", push(stk,""""))
   else if a_i ="&br"_1 
   then if subseq(a, i + 1, i + 2)="&{ block"∨ i > 1 ∧ a_(i - 1)="&}"_1 
    then processpara(a, j, i + 1, result, stk)
    else processpara(a, j, i + 1, result + EOL +"<br>"+ space, stk)
   else if a_i ="&{"_1 
   then if a_(i + 1)="block"_1 
    then processpara(a, j, i + 2, result +"<span class = block>"+ space, push(stk,"</span>"))
    else if a_(i + 1)="keyword"_1 
    then processpara(a, j, i + 2, result +"<span class = keywords>"+ space, push(stk,"</span>"))
    else if a_(i + 1)="noformat"_1 
    then let t = findindex("&}"_1, a, i + 2)
     processpara(a, j, t + 1, result + subseq(a, i + 2, t - 1), stk)
    else if a_(i + 1)="select"_1 
    then if i + 4 < length.a ∧ a_(i + 3)="&section"_1 
     then processpara(a, j, i + 4, result + EOL +"<h2 id ="+ a_(i + 2)+"onclick =""javascript:cmd5(this)"">"+ space, push(stk,"</h2>"))
     else processpara(a, j, i + 3, result + EOL +"<p id ="+ a_(i + 2)+"onclick =""javascript:cmd5(this)"">"+ space, push(stk,"</p>"))
    else if a_(i + 1)="table"_1 
    then processpara(a, j, i + 2, result +"<table>"+ space +"<caption>", push(push(stk,"</table>"),"</caption>"))
    else processpara(a, j, i + 2, result +"<span class ="+ a_(i + 1)+">", push(stk,"</span>"))
   else if a_i = space 
   then processpara(a, j, i + 1, result + space, stk)
   else processpara(a, j, i + 1, result + addamp(a_i), stk)
  else processpara(a, j, i + 1, result + addamp(a_i), stk)

Function processtotext(x:seq.word)seq.word processtotext(x, 1,"", empty:stack.word)

function processtotext(a:seq.word, i:int, result:seq.word, stk:stack.word)seq.word 
 if i > length.a 
  then result 
  else if a_i =""""_1 
  then let j = findindex(""""_1, a, i + 1)
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
 {"<meta charset =""UTF-8""> <style type =""text/css""> <!--span.avoidwrap { display:inline-block ; } span.keyword { color:blue ; } span.keywords { color:blue ; } span.literal { color:red ; } span.comment { color:green ; } span.block { padding:0px 0px 0px 0px ; margin:0px 0px 0px 20px ; display:block ; } form{margin:0px ; } html, body { margin:0 ; padding:0 ; height:100% ; }.container { margin:0 ; padding:0 ; height:100% ; display:-webkit-flex ; display:flex ; flex-direction:column ; }.floating-menu { margin:0 ; padding:0 ; background:yellowgreen ; padding:0.5em ; }.content { margin:0 ; padding:0.5em ;-webkit-flex:1 1 auto ; flex:1 1 auto ; overflow:auto ; height:0 ; min-height:0 ; }--> </style>"+EOL }

--> </style>"}

