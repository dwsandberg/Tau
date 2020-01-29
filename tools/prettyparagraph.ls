Module prettyparagraph

use UTF8

use format

use libscope

use seq.char

use seq.int

use seq.prettyresult

use stack.prettyresult

use stdlib

use textio

type prettyresult is record displaywidth:int, prec:int, rprec:int, text:seq.word

function result(c:control, w:seq.word)prettyresult prettyresult(@(+, displaywidth(c), 0, w), 0, 0, w)

function resultblock(c:control, w:seq.word)prettyresult prettyresult(10000, 10, 10, w)

function resulthigh(c:control, w:seq.word)prettyresult 
 prettyresult(@(+, displaywidth(c), 0, w), 10, 10, w)

function result(c:control, wrap:seq.word, seperator:seq.word, a:seq.prettyresult)prettyresult 
 let totalwidth = @(+, displaywidth, 0, a)+(length.a - 1)* @(+, displaywidth(c), 0, seperator + space)
  let s = 
   if totalwidth > 6000 
   then if @(max, displaywidth, 0, a)< 600 then divideseq(seperator, a, 10)else divideseq(seperator, a, 1)
   else @(seperator(seperator), text,"", a)
   prettyresult(totalwidth + @(+, displaywidth(c), 0, wrap + seperator)
   , 0 
   , 0 
   , if length.wrap > 1 then subseq(wrap, 1, length.wrap - 1)+ s + last.wrap else s)

Function prettyparagraph(p:seq.word)seq.word 
 if length.p < 2 
  then p 
  else 
   let key = p_1 
    if key in"Library library use"
     then"&{ block &keyword"+ p +"&}"
     else if key ="module"_1 
     then"&{ block &{ noformat <hr id = &quot"+ p_2 +"&quot > &} &keyword"+ p +"&}"
     else if key ="skip"_1 
     then 
      if p_2 in"/function /Function"
      then"&{ block"+ prettynoparse.subseq(p, 2, length.p)+"&}"
      else"&{ block"+ addbreak(control.charwidths,"&br", subseq(p, 2, length.p), 1, 0)+"&}"
     else if key in"export"
     then 
      assert false report"is this still used"+ p 
       "&keyword"+ subseq(p, 3, length.p)
     else 
      assert key in"parsedfunc"report"unknown key"+ key 
       let z = p 
        let headlength = toint.z_2 
        let head ="&keyword"+ subseq(z, 3, headlength + 2)
        let x = x(control.charwidths, p, headlength + 4, empty:stack.prettyresult)
        let t = text.x 
        let t2 = 
         if last.z ="builtinZinternal1Zinternal1"_1 ∧ z_(length.z - 1)= z_(headlength + 3)
         then subseq(t, 1, length.t - 1)+"usemangle"
         else t 
         if @(+, displaywidth(control.charwidths), 0, head)+ displaywidth.x > 6000 
          then"&{ block"+ head +"&br"+ t2 +"&}"
          else"&{ block"+ head + t2 +"&}"

function x(ctl:control, s:seq.word, i:int, stk:stack.prettyresult)prettyresult 
 if i > length.s 
  then top.stk 
  else 
  // assert i < 128 report"at top"+ [ s_i]+ subseq(s, i, length.s)+ toword.prec.top.stk + toword.rprec.top.stk // 
  let w = s_i 
    if w in"LIT PARAM"
     then x(ctl, s, i + 2, push(stk, result(ctl, [ s_(i + 1)])))
     else if w in"WORDS"
     then 
     // need to excape quotes // 
     let size = toint.s_(i + 1)
      let txt = @(+, escapequote,"", subseq(s, i + 2, i + 1 + size))
      let t = result(ctl,"&{ literal &quot"+ addbreak(ctl, [ EOL], txt, 1, 0)+"&quot &}")
       x(ctl, s, i + 2 + size, push(stk, t))
     else if w in"COMMENT"
     then 
      let size = toint.s_(i + 1)
      let txt ="//"+ subseq(s, i + 2, i + 1 + size)+"//"
      let txtwidth = @(+, displaywidth(ctl), 0, txt)
      let arg = top.stk 
      let r = 
       if displaywidth.arg + txtwidth > 6000 
       then prettyresult(10000, 2, 2,"&br"+ txt +"&br"+ text.arg)
       else prettyresult(displaywidth.arg + txtwidth, 2, 2, txt + text.arg)
       x(ctl, s, i + 2 + size, push(pop.stk, r))
     else if w ="RECORD"_1 
     then 
      let noargs = toint.s_(i + 1)
      let args = subseq(top(stk, noargs), 3, noargs)
       x(ctl, s, i + 2, push(pop(stk, noargs), result(ctl,"[]",",", args)))
     else if w ="APPLY"_1 
     then 
      let noargs = toint.s_(i + 1)
      let args = top(stk, noargs)
       // assert false report print.tree("X"_1, args)// 
       let term2 = codedown.(text.args_(noargs - 2))_1 
        let noargs2 = length.term2 - 2 - 1 
        let term1 = codedown.(text.args_(noargs - 1))_1 
        let noargs1 = length.term1 - 2 - 2 
        let t1 = 
         if noargs1 = 0 
         then result(ctl, [ term1_1_1])
         else result(ctl, [ term1_1_1]+"()",",", subseq(args, 1, noargs1))
        let t2 = 
         if noargs2 = 0 
         then result(ctl, [ term2_1_1])
         else result(ctl, [ term2_1_1]+"()",",", subseq(args, noargs1 + 1, noargs1 + noargs2))
        let t = result(ctl,"@()",",", [ t1, t2, args_(noargs1 + noargs2 + 1), args_(noargs1 + noargs2 + 2)])
         x(ctl, s, i + 2, push(pop(stk, noargs), t))
     else if w ="if"_1 
     then 
      let args = top(stk, 3)
      let width = @(+, displaywidth, 0, args)
      let r = 
       if width > 6000 
       then resultblock(ctl 
       ,"&{ block &keyword if"+ text.args_1 +"&br &keyword then"+ text.args_2 +(
        if subseq(text.args_3, 1, 4)="&{ block &keyword if"
        then"&br &keyword else"+ subseq(text.args_3, 3, length.text.args_3)
        else"&br &keyword else"+ text.args_3 +"&}"))
       else prettyresult(width + @(+, displaywidth(ctl), 0,"if then else")
       , 0 
       , 10 
       ,"&keyword if"+ text.args_1 +"&keyword then"+ text.args_2 +"&keyword else"+ text.args_3)
       x(ctl, s, i + 1, push(pop(stk, 3), r))
     else if w ="SET"_1 
     then 
      let args = top(stk, 2)
      let t ="&{ block &keyword let"+ s_(i + 1)+"="+ text.args_1 +(
       if subseq(text.args_2, 1, 4)in ["&{ block &keyword let","&{ block &keyword assert"]
       then"&br"+ subseq(text.args_2, 3, length.text.args_2)
       else"&{ block"+ text.args_2 +"&} &}")
      let r = prettyresult(10000, 0, 10, t)
       // assert i < 67 report [ toword.i, toword.prec.r, toword.rprec.r]+ text.args_1 // x(ctl, s, i + 2, push(pop(stk, 2), r))
     else if subseq(s, i, i + 1)="assertZbuiltinZwordzseq if"
     then 
      let args = top(stk, 3)
      let reportclause = 
       if displaywidth.args_3 + displaywidth.args_1 > 6000 
       then"&br report"+ text.args_3 
       else"report"+ text.args_3 
      let r = resulthigh(ctl 
      ,"&{ block &keyword assert"+ text.args_1 + reportclause +"&{ block"+ text.args_2 +"&} &}")
       x(ctl, s, i + 2, push(pop(stk, 3), r))
     else if w ="PRECORD"_1 
     then 
      let noargs = toint.s_(i + 1)
      let args = top(stk, noargs)
      let t = functioncall(ctl 
      ,"process"_1 
      , [ functioncall(ctl, getname.codedown.(text.args_(noargs - 1))_1, subseq(args, 1, noargs - 4))])
       x(ctl, s, i + 2, push(pop(stk, noargs), t))
     else if w ="siQ7AeoftypeQ3ATZQ24typesiQ7Aezlocal"_1 
     then x(ctl, s, i + 1, push(stk, result(ctl, [ merge."sizeoftype:T"])))
     else if w ="FREF"_1 
     then x(ctl, s, i + 2, push(stk, result(ctl, [ s_(i + 1)])))
     else 
      let a = codedown.w 
      let noargs = if length.a = 1 then // assume compiler option like FORCEINLINE or PROFILE // 1 else length.a - 2 
      let args = top(stk, noargs)
      let name = if length.a = 1 then w else getname.a 
      let r = 
       if noargs = 2 
       then 
        if name ="makereal"_1 
        then 
         let decimals = toint.(text.args_2)_1 
         let signplusdigits = decodeword.(text.args_1)_1 
         let isneg = signplusdigits_1 = hyphenchar 
         let digits = if isneg then subseq(signplusdigits, 2, length.signplusdigits)else signplusdigits 
         let number = zeropad(digits, decimals + 1)
         let decimalpart ="."+ encodeword.subseq(number, length.number - decimals + 1, length.number)
         let wholepart = if length.number - decimals = 0 then [ char.48]else subseq(number, 1, length.number - decimals)
          result(ctl, [ encodeword((if isneg then [ hyphenchar]else empty:seq.char)+ wholepart)]+ decimalpart)
        else if name in"_^"
        then binaryop(ctl, [ name], 1, args_1, args_2)
        else if name in"* / mod ∪ ∩"
        then binaryop(ctl, [ name], 3, args_1, args_2)
        else if name in"-"
        then binaryop(ctl, [ space, name, space], 4, args_1, args_2)
        else if name in"in +-∈ ∋"
        then binaryop(ctl, [ name], 4, args_1, args_2)
        else if name in"= < > ? ≤ ≠ ≥ >> <<"
        then binaryop(ctl, [ name], 5, args_1, args_2)
        else if name in"∧"
        then binaryop(ctl, [ name], 6, args_1, args_2)
        else if name in"∨"then binaryop(ctl, [ name], 7, args_1, args_2)else functioncall(ctl, name, args)
       else 
       // assert i < 128 report"at top"+ [ s_i]+ subseq(s, i, length.s)+ toword.prec.args_1 + toword.rprec.args_1 // 
       functioncall(ctl, name, args)
       x(ctl, s, i + 1, push(pop(stk, noargs), r))

function binaryop(ctl:control, op:seq.word, prec:int, a:prettyresult, b:prettyresult)prettyresult 
 // assert not(text.a ="3456"&and op ="+")report"CCC"+ toword.prec.b + toword.rprec.b + text.b // 
 if prec ≤ prec.b 
  then binaryop(ctl, op, prec, a, result(ctl,"()","", [ b]))
  else if prec < rprec.a 
  then binaryop(ctl, op, prec, result(ctl,"()","", [ a]), b)
  else if displaywidth.a > 6000 
  then prettyresult(displaywidth.a + displaywidth.b + @(+, displaywidth(ctl), 0, op)
  , prec 
  , max(prec, rprec.b)
  , text.a +"&br"+ op + text.b)
  else prettyresult(displaywidth.a + displaywidth.b + @(+, displaywidth(ctl), 0, op), prec, max(prec, rprec.b), text.a + op + text.b)

function addbreak(ctl:control, insert:seq.word, s:seq.word, i:int, width:int)seq.word 
 if i > length.s 
  then s 
  else if width < 5000 
  then addbreak(ctl, insert, s, i + 1, width + displaywidth(ctl, s_i))
  else addbreak(ctl, insert, subseq(s, 0, i - 1)+ insert + subseq(s, i, length.s), i, 0)

function divideseq(seperator:seq.word, b:seq.prettyresult, n:int)seq.word 
 let l =(length.b + n - 1)/ n 
   @(seperator("&br"+ seperator), breakup(seperator, b, n),"", arithseq(l, n, 1))

function breakup(seperator:seq.word, b:seq.prettyresult, len:int, i:int)seq.word 
 @(seperator(seperator), text,"", subseq(b, i, i + len - 1))

function getname(a:seq.seq.word)word 
 let b = a_1_1 
   if length.a_2 = 1 
    then b 
    else 
     let c = towords.decodeword.b 
      if length.c > 1 ∧ last.c ="T"_1 
       then merge(subseq(c, 1, length.c - 1)+ print.mytype.subseq(a_2, 1, length.a_2 - 1))
       else b

function zeropad(l:seq.char, n:int)seq.char if length.l < n then constantseq(n - length.l, char.48)+ l else l

function functioncall(ctl:control, name:word, args:seq.prettyresult)prettyresult 
 let noargs = length.args 
   if noargs = 1 
    then 
     if name ="-"_1 
     then 
      if 2 < prec.args_1 
      then 
       let r = result(ctl,"-()","", [ args_1])
        prettyresult(displaywidth.r, 2, 2, text.r)
      else prettyresult(displaywidth.args_1 + displaywidth(ctl,"-"_1), 2, 2,"-"+ text.args_1)
     else 
     // assert not(name ="print"_1)report"JKLll"+ toword.prec.args_1 // 
     // assert name &ne"PROFILE"_1 report"KL"+ toword.prec.args_1 + toword.rprec.args_1 + text.args_1 // 
     if prec.args_1 > 2 ∨ rprec.args_1 > 2 
      then prettyresult(displaywidth.args_1 + @(+, displaywidth(ctl), 0, [ name]+"()")
      , 0 
      , 0 
      , [ name]+"("+ text.args_1 +")")
      else prettyresult(displaywidth.args_1 + @(+, displaywidth(ctl), 0, [ name]+".")
      , 2 
      , 2 
      , [ name]+"."+ text.args_1)
    else if noargs = 0 then result(ctl, [ name])else result(ctl, [ name]+"()",",", args)

function charwidths seq.int 
 dseq(60 
 , [ 60, 60, 60, 60, 60, 60, 60, 60, 60, 60 
 , 60, 60, 60, 60, 60, 60, 60, 60, 60, 60 
 , 60, 60, 60, 60, 60, 60, 60, 60, 60, 60 
 , 60, 50, 43, 53, 64, 64, 103, 100, 30, 43 
 , 43, 64, 72, 33, 43, 33, 36, 64, 60, 64 
 , 64, 64, 64, 64, 64, 64, 64, 36, 36, 72 
 , 72, 72, 57, 108, 93, 86, 86, 93, 78, 72 
 , 93, 93, 43, 50, 92, 78, 114, 93, 93, 72 
 , 93, 86, 72, 78, 93, 93, 122, 93, 93, 78 
 , 43, 36, 43, 60, 65, 43, 57, 64, 57, 64 
 , 58, 40, 64, 64, 36, 36, 64, 36, 100, 64 
 , 64, 64, 64, 43, 50, 36, 64, 64, 93, 64 
 , 64, 57, 62, 26, 62, 70])

type control is record widths:seq.int

function displaywidth(c:control, w:word)int @(+,_(widths.c), 0, decodeword.w)

Function escapequote(t:word)word if t ="&quot"_1 then merge."& quot"else t

function_(s:seq.int, c:char)int if toint.c = 0 then 0 else s_(toint.c)

