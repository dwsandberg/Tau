Module pretty2

use display

use parse

use seq.prettyresult

use seq.seq.int

use seq.seq.seq.word

use seq.seq.word

use seq.tree.word

use seq.word

use stdlib

use tree.word

Function escapequote(t:tree.word)seq.word 
 if label.t =""""_1 then""""""else [ label.t]

Function addamp(w:word)word encodeword.@(+, addamp, empty:seq.int, decode.w)

Function addamp(ch:int)seq.int 
 if ch = 60 
  then @(+, decode, empty:seq.int,"&lt ;")
  else if ch = 38 then @(+, decode, empty:seq.int,"&amp ;")else [ ch]

function pretty(control:prettycontrol, t:tree.word)prettyresult pretty(length.preclist.control + 1, t, control)

function prec(preclist:seq.seq.word, pt:tree.word)int 
 let t = stripcomment.pt 
  if nosons.t = 1 ∧ label.t in"-"then 2 else prec(label.t, defaultprec)

function stripcomment(t:tree.word)tree.word 
 if label.t ="comment"_1 then stripcomment(t_1)else t

function checkbraces(control:prettycontrol, expb:prettyresult)prettyresult 
 let f = firstnonblank(text.expb, 1)
  if f ="("_1 ∨ f =""""_1 
  then wrap(control,"{", expb,"}")
  else expb

function firstnonblank(a:seq.word, i:int)word 
 if a_i ="&{"_1 
  then firstnonblank(a, i + 2)
  else if a_i in [ EOL, space,"&br"_1]then firstnonblank(a, i + 1)else a_i

type prettyresult is record displaywidth:int, multiline:boolean, text:seq.word

function prettyresult(control:prettycontrol, w:word)prettyresult 
 prettyresult(displaywidth(chrwidths.control, w), false, [ w])

function prettyresult(control:prettycontrol, w:seq.word)prettyresult 
 prettyresult(displaywidth(chrwidths.control, w), false, w)

function wrap(control:prettycontrol, pre:seq.word, p:prettyresult, post:seq.word)prettyresult 
 prettyresult(displaywidth.p + displaywidth(chrwidths.control, pre)+ displaywidth(chrwidths.control, post), false, pre + text.p + post)

function wrap(control:prettycontrol, pre:prettyresult, binary:seq.word, post:prettyresult)prettyresult 
 prettyresult(displaywidth.pre + displaywidth(chrwidths.control, binary)+ displaywidth.post, false, text.pre + binary + text.post)

function block(a:prettyresult)prettyresult 
 prettyresult(displaywidth.a + 10000, true,"&{ block"+ text.a +"&}")

function stripblock(control:prettycontrol, exp:prettyresult)prettyresult 
 if multiline.exp then prettyresult(control, subseq(text.exp, 3, length.text.exp - 1))else exp

function seperator(control:prettycontrol, s:seq.word, a:prettyresult, b:prettyresult)prettyresult 
 if length.text.a = 0 then b else wrap(control, a, s, b)

function blank prettyresult prettyresult(0, false,"")

function pretty(rprec:int, t:tree.word, control:prettycontrol)prettyresult 
 if label.t ="$wordlist"_1 
  then prettyresult(control,"&{ literal"+""""+ @(+, escapequote,"", sons.t)+""""+"&}")
  else if nosons.t = 0 
  then prettyresult(control, label.t)
  else if nosons.t = 2 ∧ @(∨, in.label.t, false, preclist.control)
  then wrap(control, if prec(preclist.control, t_1)> prec(preclist.control, t)
   then wrap(control,"(", pretty(control, t_1),")")
   else pretty(prec(preclist.control, t), t_1, control), if label.t ="-"_1 then [ space, label.t, space]else [ label.t], if prec(preclist.control, t_2)< prec(preclist.control, t)
   then pretty(rprec, t_2, control)
   else wrap(control,"(", pretty(control, t_2),")"))
  else if label.t ="let"_1 
  then let exp = checkbraces(control, pretty(control, t_3))
   let a = wrap(control,"&keyword let"+ [ label(t_1)]+"=", pretty(control, t_2),"")
   block.seperator(control,"&br", a, stripblock(control, exp))
  else if label.t ="$build"_1 
  then wrap(control,"[", let prettysons = @(+, pretty.control, empty:seq.prettyresult, sons.t)
   if @(+, displaywidth, nosons.t * 100, prettysons)< 6000 
   then @(seperator(control,","), identity, blank, prettysons)
   else if @(max, displaywidth, 0, prettysons)< 600 
   then divideseq(control, sons.t, 10)
   else @(seperator(control,","+"&br"), pretty.control, blank, sons.t),"]")
  else if label.t ="if"_1 
  then let ifexp = wrap(control,"&keyword if", pretty(control, t_1),"")
   let thenexp = wrap(control,"&keyword then", pretty(control, t_2),"")
   let elseexp = pretty(control, t_3)
   let y = if displaywidth.ifexp + displaywidth.thenexp + displaywidth.elseexp < 6000 
    then seperator(control,"&keyword else", seperator(control,"", ifexp, thenexp), elseexp)
    else let a = seperator(control,"&br", ifexp, thenexp)
    let b = wrap(control,"&keyword else", stripblock(control, elseexp),"")
    block.seperator(control,"&br", a, b)
   if rprec < length.preclist.control + 1 then wrap(control,"(", y,")")else y 
  else if label.t ="assert"_1 
  then let exp = checkbraces(control, pretty(control, t_2))
   let a = seperator(control,"", wrap(control,"&keyword assert", pretty(control, t_1),""), wrap(control,"&keyword report", pretty(control, t_3),""))
   block.seperator(control,"&br", a, stripblock(control, exp))
  else if label.t in"comment"
  then let exp = pretty(rprec, t_1, control)
   let a = prettyresult(control, @(+, label,"// &{ comment", subseq(sons.t, 2, nosons.t))+"&} //")
   if displaywidth.a + displaywidth.exp < 6000 
   then wrap(control, a,"", exp)
   else block.seperator(control,"&br", a, stripblock(control, exp))
  else if label.t ="makereal"_1 ∧ nosons.t = 2 ∧ nosons(t_1)= 0 ∧ nosons(t_2)= 0 
  then let decimals = toint.label(t_2)
   let signplusdigits = decode.label(t_1)
   let isneg = signplusdigits_1 = hyphenchar 
   let digits = if isneg then subseq(signplusdigits, 2, length.signplusdigits)else signplusdigits 
   let number = zeropad(digits, decimals + 1)
   let decimalpart ="."+ encodeword.subseq(number, length.number - decimals + 1, length.number)
   let wholepart = if length.number - decimals = 0 then [ 48]else subseq(number, 1, length.number - decimals)
   prettyresult(control, [ encodeword((if isneg then [ hyphenchar]else empty:seq.int)+ wholepart)]+ decimalpart)
  else if nosons.t = 1 
  then // handle uniary ops // 
   if label.t ="-"_1 
   then if prec(preclist.control, t_1)> prec(preclist.control, t)
    then wrap(control,"-(", pretty(control, t_1),")")
    else wrap(control,"-", pretty(control, t_1),"")
   else if rprec > 1 ∧ prec(preclist.control, t_1)= 0 
   then wrap(control, [ label.t]+".", pretty(rprec, t_1, control),"")
   else wrap(control, [ label.t]+"(", pretty(control, t_1),")")
  else wrap(control, [ label.t]+"(", @(seperator(control,","), pretty.control, prettyresult(0, false,""), sons.t),")")

function divideseq(control:prettycontrol, b:seq.tree.word, n:int)prettyresult 
 let l =(length.b + n - 1)/ n 
  @(seperator(control,", &br"), breakup(control, b, n), blank, arithseq(l, n, 1))

function breakup(control:prettycontrol, b:seq.tree.word, len:int, i:int)prettyresult 
 @(seperator(control,","), pretty.control, blank, subseq(b, i, i + len - 1))

function zeropad(l:seq.int, n:int)seq.int 
 if length.l < n then constantseq(n - length.l, 48)+ l else l

Function printnameandtype(t:tree.word, i:int)seq.word 
 {(if label(t_i)=":"_1 
  then print.lastson(t_i)
  else [ label(t_i)]+":"+ print.lastson(t_i))+ if i = nosons.t then""else","}

Function prettytree(control:prettycontrol, t:tree.word)seq.word 
 if label.t in"Function function"
  then let head ="&keyword"+ label.t + if nosons(t_1)= 1 
    then if decode(":"_1)_1 in decode.label(t_1)
     then towords.decode.label(t_1)
     else [ label(t_1)]+ print(t_1_nosons(t_1))
    else [ label(t_1)]+"("+ @(+, printnameandtype.t,"", arithseq(nosons.t - 2, 1, 3))+")"+ print(t_1_nosons(t_1))
   let phead = prettyresult(control, head)
   let def1 = checkbraces(control, pretty(control, t_2))
   if displaywidth.phead + displaywidth.def1 < 6000 
   then text.block.seperator(control,"", phead, def1)
   else text.block.seperator(control,"&br", phead, def1)
  else let result = if label.t in"sequence"
   then"&keyword type"+ label(t_1)+"is &keyword"+ label.t + @(+, printnameandtype.t,"", arithseq(nosons.t - 1, 1, 2))
   else if label.t in"struct"
   then"&keyword type"+ label(t_1)+"is &keyword record"+ @(+, printnameandtype.t,"", arithseq(nosons.t - 1, 1, 2))
   else if label.t in"use"
   then"&keyword"+ label.t + print(t_1)
   else if label.t in"Encoding encoding"
   then"&keyword type"+ label(t_1)+"is &keyword"+ label.t + print(t_2)
   else"&keyword type"+ label(t_1)
  {"&{ block"+ result +"&}"}

Function prettyexpression(control:prettycontrol, p:seq.word)seq.word text.pretty(control, expression.p)

Function prettyparagraph(control:prettycontrol, p:seq.word)seq.word 
 if length.p = 0 
  then p 
  else if p_1 in"function Function type use"
  then prettytree(control, parse(p, tree("xxx"_1)))
  else if p_1 in"Module module"
  then"&{ block &keyword module"+ subseq(p, 2, length.p)+"&}"
  else p

