Module outstream.T

use standard

use stack.seq.word

unbound setnospace(T)T

unbound nospace(T)boolean

unbound +(T, char)T

Function addspace(a:T, this:word)T addspace(a, this, false)

Function addspace(a:T, this:word, escapehtml:boolean)T
 if this = " &br"_1 then setnospace(a + char.10)
 else if this = ","_1 then \\ no space before but space after \\ a + char1.","
 else
  let wordseq = '-()].:"_^. "' + space
  let i = findindex(this, wordseq)
   if i < length.wordseq then \\ no space before or after \\ setnospace(a + (decodeword.merge.wordseq)_i)
   else
    let d = decodeword.this
    let a1 = if nospace.a then a else a + char.32
     if escapehtml then
     for @e ∈ d, acc = a1 ; acc
      + if @e = char1."<"then decodeword.first."&lt;"
      else if @e = char1."&"then decodeword.first."&amp;"else [ @e]
     else for @e ∈ d, acc = a1 ; acc + @e

function +(a:T, s:seq.char)T for @e ∈ s, acc = a ; acc + @e

function +(a:T, s:seq.word)T for @e ∈ s, acc = a ; addspace(acc, @e)

function +(a:T, w:word)T addspace(a, w)

Function processpara(x:T, t:seq.word)T processpara(t, 1, 1, x, push(empty:stack.seq.word,""))

function processpara(a:seq.word, j:int, i:int, result:T, stk:stack.seq.word)T
 if i > length.a then result
 else
  let this = a_i
   if this = "&noformat"_1 then
   let len = toint.a_(i + 1)
     processpara(a, j, i + 2 + len, result + subseq(a, i + 2, i + 1 + len), stk)
   else if this = " &keyword"_1 then
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
   else if this = " &br"_1 then
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
     let t = match:T(a, 0, i + 2)
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
   else if this = " &}"_1 ∧ not.isempty.stk then
   processpara(a, j, i + 1, result + top.stk + space, pop.stk)
   else if this = space then processpara(a, j, i + 1, result + space, stk)
   else processpara(a, j, i + 1, addspace(result, this, true), stk)

Function match:T(s:seq.word, depth:int, i:int)int
 if i > length.s then i
 else if s_i = " &{"_1 then match:T(s, depth + 1, i + 1)
 else if s_i = " &}"_1 then
 if depth = 0 then i else match:T(s, depth - 1, i + 1)
 else match:T(s, depth, i + 1)