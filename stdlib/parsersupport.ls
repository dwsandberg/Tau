Module parsersupport.T

use format

use standard

use set.word

use seq.stkele.T

use stack.stkele.T

use otherseq.token.T

use seq.token.T

type token is w:word, tokenno:int, attribute:T

type stkele is stateno:int, attribute:T

type reduction is toseq:seq.stkele.T

Export type:reduction.T

Export type:token.T

unbound attribute:T(seq.word)T

unbound action(int, seq.word, int, reduction.T)T

unbound text(T)seq.word

unbound forward(stk:T, T)T

Function ?(a:token.T, b:token.T)ordering w.a ? w.b

Function =(a:token.T, b:token.T)boolean w.a = w.b

Function_(r:reduction.T, n:int)T attribute.(toseq.r)_n

Function last(r:reduction.T)T attribute.(toseq.r)_(length.toseq.r)

Function errormessage:T(message:seq.word, input:seq.word, place:int)seq.word
 let m =" &{ literal" + message + " &}"
  m + " &br  &br" + prettynoparse.subseq(input, 1, place) + " &br" + m

type lrstate is lrpart:stack.stkele.T, matchthis:word, last:int, instring:boolean

function advance(state:lrstate.T, this:word, idx:int, input:seq.word, lextab:seq.token.T)lrstate.T
 let lrpart = lrpart.state
 let matchthis = matchthis.state
 let last = last.state
 let instring = instring.state
 let newinstring = if instring then this ≠ matchthis
 else
  this = "//"_1 ∨ this = "'"_1 ∨ this = '"'_1
  ∨ this = "\\"_1
 let newlast = if instring then last else idx
 let newmatchthis = if instring then matchthis else this
 let newlrpart = if newinstring then \\ in comment or string \\ lrpart
 else
  let lexindex = binarysearch(lextab, token(this, 0, attribute:T("")))
   if lexindex < 0 then
   \\ next is not in lex table \\
    let kind = checkinteger.this
     assert kind ≠ "ILLEGAL"_1 report"Illegal character in Integer" + this
      step(lrpart, input, attribute:T([ this]), if kind = "WORD"_1 then Wtoken:T else Itoken:T, idx)
   else
    let tok = lextab_lexindex
     step(lrpart, input, if instring then attribute:T(subseq(input, last, idx))else attribute.tok, tokenno.tok, idx)
  lrstate(newlrpart, newmatchthis, newlast, newinstring)

function step(stk:stack.stkele.T, input:seq.word, attrib:T, tokenno:int, place:int)stack.stkele.T
 let stateno = stateno.top.stk
 let actioncode = actiontable:T_(tokenno + length.tokenlist:T * stateno)
  if actioncode > 0 then
  if stateno = 2 then stk else push(stk, stkele(actioncode, forward(attribute.top.stk, attrib)))
  else
   assert actioncode < 0 report errormessage:T(if text.attrib = "#"then"parse error:unexpected end of paragraph"else"parse error state", input, place)
   + " &br"
   + expect:T(stateno)
   let ruleno =-actioncode
   let rulelen = rulelength:T_ruleno
   let newstk = pop(stk, rulelen)
   let newstateno = actiontable:T_(leftside:T_ruleno + length.tokenlist:T * stateno.top.newstk)
    assert newstateno > 0 report"????"
    let newstkele = stkele(newstateno, action(ruleno, input, place, reduction.top(stk, rulelen)))
     step(push(newstk, newstkele), input, attrib, tokenno, place)

function expect:T(stateno:int)seq.word
 let l = for @e ∈ arithseq(length.tokenlist:T, 1, 1), acc ="",,, acc + kk:T(stateno, @e)
  "Expecting:" + toseq(asset.l ∩ asset."]})else then report")

function kk:T(stateno:int, token:int)seq.word
 if 0 ≠ actiontable:T_(length.tokenlist:T * stateno + token)then [ tokenlist:T_token]
 else empty:seq.word

function tokenx(tokenno:int, attribute:T)token.T token("??"_1, tokenno, attribute)

Function parse:T(input:seq.word)T
 \\ if parse is called many times caching lextable improves performance \\ parse:T(attribute:T(""), sort.lextable:T, input)

Function parse:T(initial:T, lextable:seq.token.T, input:seq.word)T
 let state0 = lrstate(push(empty:stack.stkele.T, stkele(startstate:T, initial)),"'"_1, 0, false)
 let state = for e ∈ input + "#", acc = state0, i, , advance(acc, e, i, input, lextable)
  attribute.top.lrpart.state

Function sortedlextable:T seq.token.T sort.lextable:T



function Wtoken:T int \\ generated by genlex module in tools \\ 30 

function Itoken:T int \\ generated by genlex module in tools \\ 17 

function lextable:T seq.token.T \\ generated by genlex module in tools \\ [ 
token("#"_1, 19, attribute:T("#")) 
, token("$wordlist"_1, 27, attribute:T("$wordlist")) 
, token("'"_1, 27, attribute:T("'")) 
, token("("_1, 3, attribute:T("(")) 
, token(")"_1, 4, attribute:T(")")) 
, token("*"_1, 10, attribute:T("*")) 
, token("+"_1, 8, attribute:T("+")) 
, token(","_1, 12, attribute:T(",")) 
, token("-"_1, 8, attribute:T("-")) 
, token("."_1, 1, attribute:T(".")) 
, token("/"_1, 10, attribute:T("/")) 
, token("0"_1, 17, attribute:T("0")) 
, token("2"_1, 17, attribute:T("2")) 
, token(":"_1, 5, attribute:T(":")) 
, token(";"_1, 15, attribute:T(";")) 
, token("<"_1, 6, attribute:T("<")) 
, token("<<"_1, 10, attribute:T("<<")) 
, token("="_1, 2, attribute:T("=")) 
, token(">"_1, 6, attribute:T(">")) 
, token(">>"_1, 10, attribute:T(">>")) 
, token("?"_1, 6, attribute:T("?")) 
, token("Function"_1, 30, attribute:T("Function")) 
, token("I"_1, 17, attribute:T("I")) 
, token("T"_1, 30, attribute:T("T")) 
, token("W"_1, 30, attribute:T("W")) 
, token("["_1, 13, attribute:T("[")) 
, token("\"_1, 30, attribute:T("\")) 
, token("\\"_1, 11, attribute:T("\\")) 
, token("]"_1, 7, attribute:T("]")) 
, token("^"_1, 14, attribute:T("^")) 
, token("_"_1, 14, attribute:T("_")) 
, token("a"_1, 30, attribute:T("a")) 
, token("assert"_1, 23, attribute:T("assert")) 
, token("do"_1, 31, attribute:T("do")) 
, token("else"_1, 21, attribute:T("else")) 
, token("empty"_1, 30, attribute:T("empty")) 
, token("endx"_1, 29, attribute:T("endx")) 
, token("for"_1, 9, attribute:T("for")) 
, token("function"_1, 30, attribute:T("function")) 
, token("i"_1, 30, attribute:T("i")) 
, token("if"_1, 18, attribute:T("if")) 
, token("in"_1, 30, attribute:T("in")) 
, token("inst"_1, 30, attribute:T("inst")) 
, token("int"_1, 30, attribute:T("int")) 
, token("is"_1, 16, attribute:T("is")) 
, token("let"_1, 22, attribute:T("let")) 
, token("mod"_1, 10, attribute:T("mod")) 
, token("mytype"_1, 30, attribute:T("mytype")) 
, token("report"_1, 24, attribute:T("report")) 
, token("seq"_1, 30, attribute:T("seq")) 
, token("then"_1, 20, attribute:T("then")) 
, token("use"_1, 30, attribute:T("use")) 
, token("while"_1, 28, attribute:T("while")) 
, token("word"_1, 30, attribute:T("word")) 
, token("∈"_1, 8, attribute:T("∈")) 
, token("∉"_1, 8, attribute:T("∉")) 
, token("∧"_1, 25, attribute:T("∧")) 
, token("∨"_1, 26, attribute:T("∨")) 
, token("∩"_1, 10, attribute:T("∩")) 
, token("∪"_1, 10, attribute:T("∪")) 
, token("≠"_1, 6, attribute:T("≠")) 
, token("≤"_1, 6, attribute:T("≤")) 
, token("≥"_1, 6, attribute:T("≥")) 
, token('"'_1, 27, attribute:T('"')) 
, token(merge("&"+"and"), 25, attribute:T("∧")) 
, token(merge("&"+"cap"), 10, attribute:T("∩")) 
, token(merge("&"+"cup"), 10, attribute:T("∪")) 
, token(merge("&"+"ge"), 6, attribute:T("≥")) 
, token(merge("&"+"in"), 8, attribute:T("∈")) 
, token(merge("&"+"le"), 6, attribute:T("≤")) 
, token(merge("&"+"ne"), 6, attribute:T("≠")) 
, token(merge("&"+"nin"), 8, attribute:T("∉")) 
, token(merge("&"+"or"), 26, attribute:T("∨"))]

function rulelength:T seq.int [ 2, 7, 7, 7, 7, 7, 7, 7, 7, 4, 4, 2, 1, 1, 3, 3, 5, 4, 6, 1, 4, 3, 6, 3, 2, 3, 3, 3, 3, 3, 3, 3, 1, 3, 3, 3, 3, 5, 1, 3, 1, 3, 1, 2, 1, 3, 11, 10, 3, 4, 1, 2, 3, 5, 1, 8, 11]

function leftside:T seq.int [ 43, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 40, 32, 32, 32, 32, 32, 32, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 34, 34, 37, 41, 37, 37, 37, 37, 33, 33, 37, 37, 44, 44, 35, 35, 37, 37, 36, 36, 38, 38, 39, 37, 37]

function tokenlist:T seq.word".=():>]-for * comment, [_; is I if # then else let assert report ∧ ∨ $wordlist while endx W do P T L B D E F1 F2 FP A F G NM"

function startstate:T int 1

function finalstate:T int 2

noactions 2055 
nosymbols:44 
norules 57 
nostate 180
 
function actiontable:T seq.int [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 9, 0, 11, 0, 7, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 13, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -45, -45, -45, 19, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 0, 29, 30, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 0, 29, 30, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 0, 29, 30, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 0, 29, 30, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 0, 29, 30, 0, 0, 0, 0, 0, 0, 37, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 0, 29, 30, 0, 0, 0, 0, 0, 0, 38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 0, 29, 30, 0, 0, 0, 0, 0, 0, 39, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 0, 40, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 48, 0, 0, 0, 0, 0, 0, 53, 55, -41, -41, -41, 0, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 0, 29, 30, 0, 0, 0, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -13, 0, 0, 0, 0, 0, 0, 0, 58, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -14, 0, 0, 0, 0, 0, 0, 0, -14, 0, 0, 0, 0, 0, 0, -14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55, -41, -41, -41, 59, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 60, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -46, -46, -46, 0, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 63, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 66, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58, 0, 0, 0, 0, 0, 0, -11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 67, 0, 0, 0, 0, 0, 0, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 70, 0, 0, 0, 0, 0, 0, 0, 71, 72, 0, 0, 0, 0, 0, 0, -43, -43, -43, 0, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, 0, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 73, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 74, 0, 0, 0, 0, 0, 0, 53, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 75, 0, 0, 0, 0, 0, 0, 53, 76, -45, -45, -45, 19, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, 0, 0, 79, 0, 80, 0, 77, 0, 0, 0, 83, 0, 0, 0, 0, -10, 0, 0, 0, 0, 0, 81, 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 84, 0, 0, 0, 0, 0, 0, 53, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 85, 0, 0, 0, 0, 0, 0, 53, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 86, 0, 0, 0, 0, 0, 0, 53, 87, -39, -39, -39, 0, -39, -39, -39, -39, -39, -39, -39, -39, -39, -39, 0, -39, -39, -39, -39, -39, -39, -39, -39, -39, -39, -39, -39, -39, -39, -39, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -20, 88, -20, 0, -20, -20, -20, -20, -20, -20, -20, -20, -20, -20, 0, -20, -20, -20, -20, -20, -20, -20, -20, -20, -20, -20, -20, -20, -20, -20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 89, 45, 0, 90, 0, 0, 0, 0, 0, 0, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 91, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 92, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 93, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 94, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96, 0, 0, 95, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 97, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 98, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 102, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 103, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 104, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, -44, -44, 0, 79, -44, 80, -44, 77, -44, -44, -44, 83, -44, 0, -44, -44, -44, -44, -44, -44, -44, -44, 81, 82, -44, -44, -44, -44, -44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 105, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 106, 0, 0, 0, 0, 0, 0, 53, 0, 107, 0, 0, 0, 0, 0, 108, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 109, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -55, 0, 0, -55, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 111, 0, 0, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 112, 113, 0, 0, 0, 0, 0, 0, 53, 0, 78, 0, 0, 0, 79, 0, 80, 0, 77, 0, 114, 0, 83, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 81, 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, 0, 0, 79, 0, 80, 0, 77, 0, 0, 0, 83, 0, 0, 0, 0, 0, 0, 0, 0, 0, 115, 81, 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 116, 0, 0, 0, 0, 0, 0, 53, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 117, 0, 0, 0, 0, 0, 0, 53, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 118, 0, 0, 0, 0, 0, 0, 53, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 119, 0, 0, 0, 0, 0, 0, 53, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 120, 0, 0, 0, 0, 0, 0, 53, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 121, 0, 0, 0, 0, 0, 0, 53, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 122, 0, 0, 0, 0, 0, 0, 53, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 123, 0, 0, 0, 0, 0, 0, 53, 0, -25, -25, -25, 0, -25, -25, -25, -25, -25, -25, -25, -25, 83, -25, 0, -25, -25, -25, -25, -25, -25, -25, -25, -25, -25, -25, -25, -25, -25, -25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, 0, 0, 79, 0, 80, 0, 77, 0, 0, 0, 83, 0, 0, 0, 0, 0, 124, 0, 0, 0, 0, 81, 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, 125, 0, 79, 0, 80, 0, 77, 0, 0, 0, 83, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 81, 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 126, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 127, 45, 0, 90, 0, 0, 0, 0, 0, 0, 53, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 129, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, -33, 0, 79, -33, 80, 0, 77, 0, -33, 0, 83, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 81, 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -42, -42, -42, 0, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 130, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 131, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 132, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -15, 0, 0, 0, 0, 0, 0, 0, -15, 0, 0, 0, 0, 0, 0, -15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55, -41, -41, -41, 133, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -16, 0, 0, 0, 0, 0, 0, 0, -16, 0, 0, 0, 0, 0, 0, -16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 134, 0, 0, 0, 0, 0, 0, 53, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 135, 0, 0, 0, 0, 0, 0, 53, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 136, 0, 0, 0, 0, 0, 0, 53, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 137, 0, 0, 0, 0, 0, 0, 53, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 138, 0, 0, 0, 0, 0, 0, 53, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 139, 0, 0, 0, 0, 0, 0, 53, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 140, 0, 0, 0, 0, 0, 0, 53, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 141, 0, 0, 0, 0, 0, 0, 53, 0, 78, -37, -37, 0, 79, -37, 80, -37, 77, -37, -37, -37, 83, -37, 0, -37, -37, -37, -37, -37, -37, -37, -37, 81, 82, -37, -37, -37, -37, -37, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 142, 0, 0, 0, 0, 0, 0, 53, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 143, 0, 0, 0, 0, 0, 0, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 145, 0, 0, 0, 0, 0, 0, 53, 0, 0, 146, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -49, -49, -49, 0, -49, -49, -49, -49, -49, -49, -49, -49, -49, -49, 0, -49, -49, -49, -49, -49, -49, -49, -49, -49, -49, -49, -49, -49, -49, -49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, -51, -51, 0, 79, -51, 80, -51, 77, -51, -51, -51, 83, 147, 0, -51, -51, -51, -51, -51, -51, -51, -51, 81, 82, -51, -51, -51, -51, -51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 148, 113, 0, 0, 0, 0, 0, 0, 53, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 149, 113, 0, 0, 0, 0, 0, 0, 53, 0, -26, -26, -26, 0, -26, -26, -26, -26, -26, -26, -26, -26, 83, -26, 0, -26, -26, -26, -26, -26, -26, -26, -26, -26, -26, -26, -26, -26, -26, -26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -27, -27, -27, 0, -27, -27, -27, -27, -27, -27, -27, -27, 83, -27, 0, -27, -27, -27, -27, -27, -27, -27, -27, -27, -27, -27, -27, -27, -27, -27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -29, -29, -29, 0, -29, -29, 80, -29, 77, -29, -29, -29, 83, -29, 0, -29, -29, -29, -29, -29, -29, -29, -29, -29, -29, -29, -29, -29, -29, -29, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -30, -30, -30, 0, -30, -30, 80, -30, 77, -30, -30, -30, 83, -30, 0, -30, -30, -30, -30, -30, -30, -30, -30, -30, -30, -30, -30, -30, -30, -30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -28, -28, -28, 0, -28, -28, -28, -28, 77, -28, -28, -28, 83, -28, 0, -28, -28, -28, -28, -28, -28, -28, -28, -28, -28, -28, -28, -28, -28, -28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, -31, -31, 0, 79, -31, 80, -31, 77, -31, -31, -31, 83, -31, 0, -31, -31, -31, -31, -31, -31, -31, -31, -31, -31, -31, -31, -31, -31, -31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, -32, -32, 0, 79, -32, 80, -32, 77, -32, -32, -32, 83, -32, 0, -32, -32, -32, -32, -32, -32, -32, -32, 81, -32, -32, -32, -32, -32, -32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -24, -24, -24, 0, -24, -24, -24, -24, -24, -24, -24, -24, -24, -24, 0, -24, -24, -24, -24, -24, -24, -24, -24, -24, -24, -24, -24, -24, -24, -24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 150, 0, 0, 0, 0, 0, 0, 53, 0, -22, -22, -22, 0, -22, -22, -22, -22, -22, -22, -22, -22, -22, -22, 0, -22, -22, -22, -22, -22, -22, -22, -22, -22, -22, -22, -22, -22, -22, -22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -40, -40, -40, 0, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, 0, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 151, 0, 0, 0, 0, 0, 0, 0, 129, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -35, -35, -35, 0, -35, -35, -35, -35, -35, -35, -35, -35, -35, -35, 0, -35, -35, -35, -35, -35, -35, -35, -35, -35, -35, -35, -35, -35, -35, -35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 152, 0, 0, 0, 0, 0, 0, 53, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 153, 0, 0, 0, 0, 0, 0, 53, 0, 0, 0, -18, 0, 0, 0, 0, 0, 0, 0, -18, 0, 0, 0, 0, 0, 0, -18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 154, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 155, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, 0, 0, 79, 0, 80, 0, 77, 0, 0, 0, 83, 0, 0, 0, 0, -7, 0, 0, 0, 0, 0, 81, 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, 0, 0, 79, 0, 80, 0, 77, 0, 0, 0, 83, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, 81, 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, 0, 0, 79, 0, 80, 0, 77, 0, 0, 0, 83, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 81, 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, 0, 0, 79, 0, 80, 0, 77, 0, 0, 0, 83, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 81, 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, 0, 0, 79, 0, 80, 0, 77, 0, 0, 0, 83, 0, 0, 0, 0, -8, 0, 0, 0, 0, 0, 81, 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, 0, 0, 79, 0, 80, 0, 77, 0, 0, 0, 83, 0, 0, 0, 0, -9, 0, 0, 0, 0, 0, 81, 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, 0, 0, 79, 0, 80, 0, 77, 0, 0, 0, 83, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 81, 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, -36, 0, 0, 79, 0, 80, -36, 77, -36, 0, -36, 83, 0, 0, -36, -36, 0, 0, 0, -36, -36, 0, 81, 82, -36, 0, 0, -36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, 0, 0, 79, 0, 80, 0, 77, 0, -53, 0, 83, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 81, 82, 0, -53, 0, 0, -53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, 0, 0, 79, 0, 80, 0, 77, 0, 156, 0, 83, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 81, 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 157, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, 0, 0, 79, 0, 80, 0, 77, 0, 0, 0, 83, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 81, 82, 0, 0, 158, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 159, 0, 0, 0, 0, 0, 0, 53, 0, -52, -52, -52, 0, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, 0, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -50, -50, -50, 0, -50, -50, -50, -50, -50, -50, -50, -50, -50, -50, 0, -50, -50, -50, -50, -50, -50, -50, -50, -50, -50, -50, -50, -50, -50, -50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 160, 0, 0, 0, 0, 0, 0, 53, 0, 78, 0, 0, 0, 79, 0, 80, 0, 77, 0, 0, 0, 83, 0, 0, 0, 0, 0, 0, 161, 0, 0, 0, 81, 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -21, -21, -21, 0, -21, -21, -21, -21, -21, -21, -21, -21, -21, -21, 0, -21, -21, -21, -21, -21, -21, -21, -21, -21, -21, -21, -21, -21, -21, -21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, -34, 0, 79, -34, 80, 0, 77, 0, -34, 0, 83, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 81, 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, 0, 0, 79, 0, 80, 0, 77, 0, 0, 0, 83, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 81, 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 162, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -17, 0, 0, 0, 0, 0, 0, 0, -17, 0, 0, 0, 0, 0, 0, -17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 163, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 164, 0, 0, 0, 0, 0, 0, 53, 0, 0, 165, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, 166, 0, 79, 0, 80, 0, 77, 0, 0, 0, 83, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 81, 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, -38, -38, 0, 79, -38, 80, -38, 77, -38, -38, -38, 83, -38, 0, -38, -38, -38, -38, -38, -38, -38, -38, 81, 82, -38, -38, -38, -38, -38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 167, 113, 0, 0, 0, 0, 0, 0, 53, 0, 0, 0, -19, 0, 0, 0, 0, 0, 0, 0, -19, 0, 0, 0, 0, 0, 0, -19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 168, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, 0, 0, 79, 0, 80, 0, 77, 0, -54, 0, 83, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 81, 82, 0, -54, 0, 0, -54, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 169, 0, 0, 0, 0, 0, 0, 53, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 170, 0, 0, 0, 0, 0, 0, 53, 0, -23, -23, -23, 0, -23, -23, -23, -23, -23, -23, -23, -23, -23, -23, 0, -23, -23, -23, -23, -23, -23, -23, -23, -23, -23, -23, -23, -23, -23, -23, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 171, 0, 0, 0, 0, 0, 0, 53, 0, 78, 0, 172, 0, 79, 0, 80, 0, 77, 0, 0, 0, 83, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 81, 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, 0, 0, 79, 0, 80, 0, 77, 0, 0, 0, 83, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 81, 82, 0, 0, 173, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, 0, 0, 79, 0, 80, 0, 77, 0, 174, 0, 83, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 81, 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -56, -56, -56, 0, -56, -56, -56, -56, -56, -56, -56, -56, -56, -56, 0, -56, -56, -56, -56, -56, -56, -56, -56, -56, -56, -56, -56, -56, -56, -56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 175, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 176, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 177, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 49, 43, 0, 41, 0, 54, 0, 0, 0, 52, 50, 0, 0, 0, 42, 46, 0, 0, 0, 44, 0, 0, 47, 0, 0, 0, 0, 45, 0, 178, 0, 0, 0, 0, 0, 0, 53, 0, 0, -48, 0, 0, 0, 0, -48, -48, 0, -48, -48, -48, 0, 0, 0, -48, -48, 0, 0, 0, -48, -48, 0, 0, 0, -48, 0, 0, -48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 179, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, 180, 0, 79, 0, 80, 0, 77, 0, 0, 0, 83, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 81, 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -47, 0, 0, 0, 0, -47, -47, 0, -47, -47, -47, 0, 0, 0, -47, -47, 0, 0, 0, -47, -47, 0, 0, 0, -47, 0, 0, -47, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -57, -57, -57, 0, -57, -57, -57, -57, -57, -57, -57, -57, -57, -57, 0, -57, -57, -57, -57, -57, -57, -57, -57, -57, -57, -57, -57, -57, -57, -57]



