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

Function _(r:reduction.T, n:int)T attribute.(toseq.r)_n

Function last(r:reduction.T)T attribute.(toseq.r)_(length.toseq.r)

Function errormessage:T(message:seq.word, input:seq.word, place:int)seq.word
let m = " /< literal" + message + " />"
m + " /br  /br" + prettynoparse.subseq(input, 1, place) + " /br" + m

Function parse:T(initial:T, lextable:seq.token.T, input:seq.word)T
for lrpart = push(empty:stack.stkele.T, stkele(startstate:T, initial))
, matchthis = singlequote_1
, last = 0
, instring = false
, idx = 1
, nesting = 0
, this ∈ input + "#"
while stateno.top.lrpart ≠ finalstate:T
do if instring ∧ this ≠ matchthis ∨ nesting > 0 then
  {in comment or string}
  let nestingchange = 
   if matchthis ≠ "}"_1 then 0
   else if nesting > 0 ∧ matchthis = this then-1
   else if this = "{"_1 then 1 else 0
  next(lrpart, matchthis, last, true, idx + 1, nesting + nestingchange)
 else if not.instring ∧ ( this = singlequote_1 ∨  this = dq_1 ∨ this = "{"_1)then
  {start string}
  next(lrpart
  , if this = "{"_1 then"}"_1 else this
  , idx
  , true
  , idx + 1
  , nesting
  )
 else
  let lexindex = binarysearch(lextable, token(this, 0, attribute:T("")))
  let newlrpart = 
   if lexindex < 0 then
    {next is not in lex table}
    let kind = checkinteger.this
    assert kind ≠ "ILLEGAL"_1 report"Illegal character in Integer" + this
    step(lrpart
    , input
    , attribute:T([this])
    , if kind = "WORD"_1 then Wtoken:T else Itoken:T
    , idx
    )
   else
    let tok = lextable_lexindex
    step(lrpart
    , input
    , if instring then attribute:T(subseq(input, last, idx))else attribute.tok
    , tokenno.tok
    , idx
    )
  next(newlrpart, this, idx, false, idx + 1, nesting)
/for(assert not.instring report errormessage:T("missing string terminator", input, last)
attribute.undertop(lrpart,1))

function step(stk:stack.stkele.T, input:seq.word, attrib:T, tokenno:int, place:int)stack.stkele.T
let stateno = stateno.top.stk
let actioncode = actiontable:T_(tokenno + length.tokenlist:T * stateno)
if actioncode > 0 then
 if stateno = finalstate:T then stk
  else push(stk, stkele(actioncode, forward(attribute.top.stk, attrib)))
else
 assert actioncode < 0
 report errormessage:T(if text.attrib = "#"then"parse error:unexpected end of paragraph"
 else"parse error state"
 , input
 , place
 )
 + " /br"
 + expect:T(stateno)
 let ruleno = -actioncode
 let rulelen = rulelength:T_ruleno
 let newstk = pop(stk, rulelen)
 let newstateno = actiontable:T_(leftside:T_ruleno + length.tokenlist:T * stateno.top.newstk)
 assert newstateno > 0 report"????"
 let newstkele = stkele(newstateno, action(ruleno, input, place, reduction.top(stk, rulelen)))
 step(push(newstk, newstkele), input, attrib, tokenno, place)

function expect:T(stateno:int)seq.word
let l = 
 for acc = "", @e ∈ arithseq(length.tokenlist:T, 1, 1)do acc + kk:T(stateno, @e)/for(acc)
"Expecting:" + toseq(asset.l ∩ asset."]})else then report")

function kk:T(stateno:int, token:int)seq.word
if 0 ≠ actiontable:T_(length.tokenlist:T * stateno + token)then[tokenlist:T_token]
else empty:seq.word

function tokenx(tokenno:int, attribute:T)token.T token("??"_1, tokenno, attribute)

Function parse:T(input:seq.word)T
{if parse is called many times caching lextable improves performance}
parse:T(attribute:T(""), sort.lextable:T, input)

Function sortedlextable:T seq.token.T sort.lextable:T

function Wtoken:T int{generated by genlex module in tools}30

function Itoken:T int{generated by genlex module in tools}17

function lextable:T seq.token.T
{generated by genlex module in tools}
[token("#"_1, 19, attribute:T("#"))
, token("$wordlist"_1, 27, attribute:T("$wordlist"))
, token(singlequote_1, 27, attribute:T(singlequote))
, token("("_1, 3, attribute:T("("))
, token(")"_1, 4, attribute:T(")"))
, token("*"_1, 10, attribute:T("*"))
, token("+"_1, 8, attribute:T("+"))
, token(", "_1, 12, attribute:T(", "))
, token("-"_1, 8, attribute:T("-"))
, token("."_1, 1, attribute:T("."))
, token(". "_1, 1, attribute:T("."))
, token("/"_1, 10, attribute:T("/"))
, token("/for"_1, 29, attribute:T("/for"))
, token("/if"_1, 15, attribute:T("/if"))
, token("0"_1, 17, attribute:T("0"))
, token("2"_1, 17, attribute:T("2"))
, token(":"_1, 5, attribute:T(":"))
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
, token("\"_1, 10, attribute:T("\"))
, token("]"_1, 7, attribute:T("]"))
, token("^"_1, 14, attribute:T("^"))
, token("_"_1, 14, attribute:T("_"))
, token("a"_1, 30, attribute:T("a"))
, token("assert"_1, 23, attribute:T("assert"))
, token("do"_1, 31, attribute:T("do"))
, token("else"_1, 21, attribute:T("else"))
, token("empty"_1, 30, attribute:T("empty"))
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
, token("}"_1, 11, attribute:T("}"))
, token("∈"_1, 8, attribute:T("∈"))
, token("∉"_1, 8, attribute:T("∉"))
, token("∧"_1, 25, attribute:T("∧"))
, token("∨"_1, 26, attribute:T("∨"))
, token("∩"_1, 10, attribute:T("∩"))
, token("∪"_1, 10, attribute:T("∪"))
, token("≠"_1, 6, attribute:T("≠"))
, token("≤"_1, 6, attribute:T("≤"))
, token("≥"_1, 6, attribute:T("≥"))
, token(dq_1, 27, attribute:T(dq))
, token(merge("/" + "and"), 25, attribute:T("∧"))
, token(merge("/" + "cap"), 10, attribute:T("∩"))
, token(merge("/" + "cup"), 10, attribute:T("∪"))
, token(merge("/" + "ge"), 6, attribute:T("≥"))
, token(merge("/" + "in"), 8, attribute:T("∈"))
, token(merge("/" + "le"), 6, attribute:T("≤"))
, token(merge("/" + "ne"), 6, attribute:T("≠"))
, token(merge("/" + "nin"), 8, attribute:T("∉"))
, token(merge("/" + "or"), 26, attribute:T("∨"))
]

function rulelength:T seq.int
[2, 7, 7, 7, 7, 7, 7, 7, 7, 4, 4, 1, 1, 3, 3, 5, 4, 6, 1, 4, 3, 6, 7, 3, 2
, 3, 3, 3, 3, 3, 3, 3, 1, 3, 3, 3, 3, 5, 1, 3, 1, 3, 1, 2, 1, 3, 3, 5, 5, 8
, 10, 1]

function leftside:T seq.int
[42, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 38, 33, 33, 33, 33, 33, 33, 37, 37, 37, 37, 37, 37, 37
, 37, 37, 37, 37, 37, 37, 37, 35, 35, 37, 39, 37, 37, 37, 37, 34, 34, 37, 37, 43, 43, 41, 41, 32, 37
, 37, 36]

function tokenlist:T seq.word
".=():>]-for * comment, [_/if is I if # then else let assert report ∧ ∨ $wordlist while /for W do F2 P T L D E FP A F F1 G NM"

function startstate:T int 1

function finalstate:T int 4

noactions 1836 nosymbols:43 norules 52 nostate 163

function actiontable:T seq.int
[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 7, 0, 9, 0, 5, 0
, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 11, 0, 0, 0, 8, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, -45, -45, -45, 17, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45
, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 23, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 0, 0, 27, 28, 0, 0, 0, 30
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 0, 0, 27, 28, 0
, 0, 0, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 0, 0
, 27, 28, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 24, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 29, 0, 0, 27, 28, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 29, 0, 0, 27, 28, 0, 0, 0, 35, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 0, 0, 27, 28, 0, 0, 0, 36, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 0, 0, 27, 28, 0, 0, 0
, 37, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 0, 0, 38, 28
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 46, 41, 0, 39
, 0, 51, 0, 0, 0, 49, 47, 0, 0, 0, 40, 43, 0, 0, 0, 42, 0, 0, 44, 0
, 0, 0, 0, 0, 0, 45, 0, 0, 0, 0, 0, 50, 52, -41, -41, -41, 0, -41, -41, -41
, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41
, -41, -41, -41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 29, 0, 0, 27, 28, 0, 0, 0, 53, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 54, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, -12, 0, 0, 0, 0, 0, 0, 0, 55, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, -13, 0, 0, 0, 0, 0, 0, 0, -13, 0, 0, 0, 0
, 0, 0, -13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 52, -41, -41, -41, 56, -41, -41, -41, -41, -41, -41, -41, -41
, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 59
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, -46, -46, -46, 0, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46
, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 60, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 61, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 63, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 55, 0, 0, 0, 0, 0, 0, -11, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48
, 0, 0, 0, 0, 46, 41, 0, 39, 0, 51, 0, 0, 0, 49, 47, 0, 0, 0, 40, 43
, 0, 0, 0, 42, 0, 0, 44, 0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 50
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65, 0, 0, 0, 0, 0, 0, 0, 0, 66, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 0, 67, 0, 0, 0, 0, 0
, 0, 0, 0, 69, 0, 0, 0, -43, -43, -43, 0, -43, -43, -43, -43, -43, -43, -43, -43, -43
, -43, 0, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 46, 41, 0, 39
, 0, 51, 0, 0, 0, 49, 47, 0, 0, 0, 40, 43, 0, 0, 0, 42, 0, 0, 44, 0
, 0, 0, 0, 0, 0, 70, 0, 0, 0, 0, 0, 50, 71, -45, -45, -45, 17, -45, -45, -45
, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45
, -45, -45, -45, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 0, 0, 0
, 74, 0, 75, 0, 72, 0, 0, 0, 78, 0, 0, 0, 0, -10, 0, 0, 0, 0, 0, 76
, 77, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 48, 0, 0, 0, 0, 46, 41, 0, 39, 0, 51, 0, 0, 0, 49, 47, 0, 0, 0, 40
, 43, 0, 0, 0, 42, 0, 0, 44, 0, 0, 0, 0, 0, 0, 79, 0, 0, 0, 0, 0
, 50, 0, 0, 48, 0, 0, 0, 0, 46, 41, 0, 39, 0, 51, 0, 0, 0, 49, 47, 0
, 0, 0, 40, 43, 0, 0, 0, 42, 0, 0, 44, 0, 0, 0, 0, 0, 0, 80, 0, 0
, 0, 0, 0, 50, 0, 0, 48, 0, 0, 0, 0, 46, 41, 0, 39, 0, 51, 0, 0, 0
, 49, 47, 0, 0, 0, 40, 43, 0, 0, 0, 42, 0, 0, 44, 0, 0, 0, 0, 0, 0
, 81, 0, 0, 0, 0, 0, 50, 82, -39, -39, -39, 0, -39, -39, -39, -39, -39, -39, -39, -39
, -39, -39, 0, -39, -39, -39, -39, -39, -39, -39, -39, -39, -39, -39, -39, -39, -39, -39, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -19, 83, -19, 0, -19, -19, -19, -19, -19
, -19, -19, -19, -19, -19, 0, -19, -19, -19, -19, -19, -19, -19, -19, -19, -19, -19, -19, -19, -19
, -19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0
, 46, 41, 0, 39, 0, 51, 0, 0, 0, 49, 47, 0, 0, 0, 40, 43, 0, 0, 0, 42
, 0, 0, 44, 0, 0, 0, 0, 84, 0, 85, 0, 0, 0, 0, 0, 50, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 24, 0, 0, 0, 86, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 87, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 88, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 89, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 91, 0, 0, 0, 90, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0
, 0, 92, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 24, 0, 0, 0, 93, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 24, 0, 0, 0, 94, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 95, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 96, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 97, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 98
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0
, 0, 0, 99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -44, -44, -44, 0, -44, -44, -44
, -44, -44, -44, -44, -44, -44, -44, 0, -44, -44, -44, -44, -44, -44, -44, -44, -44, -44, -44, -44
, -44, -44, -44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 100, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 48, 0, 0, 0, 0, 46, 41, 0, 39, 0, 51, 0, 0, 0, 49, 47, 0, 0, 0, 40
, 43, 0, 0, 0, 42, 0, 0, 44, 0, 0, 0, 0, 0, 0, 101, 0, 0, 0, 0, 0
, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 103, 0, 0, 102, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 104, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 105, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 0, 0, 0, 74, 0, 75, 0, 72
, 0, 0, 0, 78, 0, 0, 0, 0, 0, 0, 0, 0, 0, 106, 76, 77, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0
, 46, 41, 0, 39, 0, 51, 0, 0, 0, 49, 47, 0, 0, 0, 40, 43, 0, 0, 0, 42
, 0, 0, 44, 0, 0, 0, 0, 0, 0, 107, 0, 0, 0, 0, 0, 50, 0, 0, 48, 0
, 0, 0, 0, 46, 41, 0, 39, 0, 51, 0, 0, 0, 49, 47, 0, 0, 0, 40, 43, 0
, 0, 0, 42, 0, 0, 44, 0, 0, 0, 0, 0, 0, 108, 0, 0, 0, 0, 0, 50, 0
, 0, 48, 0, 0, 0, 0, 46, 41, 0, 39, 0, 51, 0, 0, 0, 49, 47, 0, 0, 0
, 40, 43, 0, 0, 0, 42, 0, 0, 44, 0, 0, 0, 0, 0, 0, 109, 0, 0, 0, 0
, 0, 50, 0, 0, 48, 0, 0, 0, 0, 46, 41, 0, 39, 0, 51, 0, 0, 0, 49, 47
, 0, 0, 0, 40, 43, 0, 0, 0, 42, 0, 0, 44, 0, 0, 0, 0, 0, 0, 110, 0
, 0, 0, 0, 0, 50, 0, 0, 48, 0, 0, 0, 0, 46, 41, 0, 39, 0, 51, 0, 0
, 0, 49, 47, 0, 0, 0, 40, 43, 0, 0, 0, 42, 0, 0, 44, 0, 0, 0, 0, 0
, 0, 111, 0, 0, 0, 0, 0, 50, 0, 0, 48, 0, 0, 0, 0, 46, 41, 0, 39, 0
, 51, 0, 0, 0, 49, 47, 0, 0, 0, 40, 43, 0, 0, 0, 42, 0, 0, 44, 0, 0
, 0, 0, 0, 0, 112, 0, 0, 0, 0, 0, 50, 0, 0, 48, 0, 0, 0, 0, 46, 41
, 0, 39, 0, 51, 0, 0, 0, 49, 47, 0, 0, 0, 40, 43, 0, 0, 0, 42, 0, 0
, 44, 0, 0, 0, 0, 0, 0, 113, 0, 0, 0, 0, 0, 50, 0, 0, 48, 0, 0, 0
, 0, 46, 41, 0, 39, 0, 51, 0, 0, 0, 49, 47, 0, 0, 0, 40, 43, 0, 0, 0
, 42, 0, 0, 44, 0, 0, 0, 0, 0, 0, 114, 0, 0, 0, 0, 0, 50, 0, -25, -25
, -25, 0, -25, -25, -25, -25, -25, -25, -25, -25, 78, -25, 0, -25, -25, -25, -25, -25, -25, -25
, -25, -25, -25, -25, -25, -25, -25, -25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 73, 0, 0, 0, 74, 0, 75, 0, 72, 0, 0, 0, 78, 0, 0, 0, 0, 0, 115
, 0, 0, 0, 0, 76, 77, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 73, 0, 116, 0, 74, 0, 75, 0, 72, 0, 0, 0, 78, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 76, 77, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 117, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 46, 41, 0, 39
, 0, 51, 0, 0, 0, 49, 47, 0, 0, 0, 40, 43, 0, 0, 0, 42, 0, 0, 44, 0
, 0, 0, 0, 118, 0, 85, 0, 0, 0, 0, 0, 50, 0, 0, 0, 0, 0, 0, 119, 0
, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 0, -33, 0
, 74, -33, 75, 0, 72, 0, -33, 0, 78, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 76
, 77, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -42
, -42, -42, 0, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42
, -42, -42, -42, -42, -42, -42, -42, -42, -42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 121, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 122, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 123, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -14, 0, 0, 0, 0, 0, 0
, 0, -14, 0, 0, 0, 0, 0, 0, -14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52, -41, -41, -41, 124, -41, -41
, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41
, -41, -41, -41, -41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -15
, 0, 0, 0, 0, 0, 0, 0, -15, 0, 0, 0, 0, 0, 0, -15, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 48, 0, 0, 0, 0, 46, 41, 0, 39, 0, 51, 0, 0, 0, 49, 47, 0, 0, 0
, 40, 43, 0, 0, 0, 42, 0, 0, 44, 0, 0, 0, 0, 0, 0, 125, 0, 0, 0, 0
, 0, 50, 0, 0, 48, 0, 0, 0, 0, 46, 41, 0, 39, 0, 51, 0, 0, 0, 49, 47
, 0, 0, 0, 40, 43, 0, 0, 0, 42, 0, 0, 44, 0, 0, 0, 0, 0, 0, 126, 0
, 0, 0, 0, 0, 50, 0, 0, 48, 0, 0, 0, 0, 46, 41, 0, 39, 0, 51, 0, 0
, 0, 49, 47, 0, 0, 0, 40, 43, 0, 0, 0, 42, 0, 0, 44, 0, 0, 0, 0, 0
, 0, 127, 0, 0, 0, 0, 0, 50, 0, 0, 48, 0, 0, 0, 0, 46, 41, 0, 39, 0
, 51, 0, 0, 0, 49, 47, 0, 0, 0, 40, 43, 0, 0, 0, 42, 0, 0, 44, 0, 0
, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 50, 0, 0, 48, 0, 0, 0, 0, 46, 41
, 0, 39, 0, 51, 0, 0, 0, 49, 47, 0, 0, 0, 40, 43, 0, 0, 0, 42, 0, 0
, 44, 0, 0, 0, 0, 0, 0, 129, 0, 0, 0, 0, 0, 50, 0, 0, 48, 0, 0, 0
, 0, 46, 41, 0, 39, 0, 51, 0, 0, 0, 49, 47, 0, 0, 0, 40, 43, 0, 0, 0
, 42, 0, 0, 44, 0, 0, 0, 0, 0, 0, 130, 0, 0, 0, 0, 0, 50, 0, 0, 48
, 0, 0, 0, 0, 46, 41, 0, 39, 0, 51, 0, 0, 0, 49, 47, 0, 0, 0, 40, 43
, 0, 0, 0, 42, 0, 0, 44, 0, 0, 0, 0, 0, 0, 131, 0, 0, 0, 0, 0, 50
, 0, 0, 48, 0, 0, 0, 0, 46, 41, 0, 39, 0, 51, 0, 0, 0, 49, 47, 0, 0
, 0, 40, 43, 0, 0, 0, 42, 0, 0, 44, 0, 0, 0, 0, 0, 0, 132, 0, 0, 0
, 0, 0, 50, 0, 73, -37, -37, 0, 74, -37, 75, -37, 72, -37, -37, -37, 78, -37, 0, -37
, -37, -37, -37, -37, -37, -37, -37, 76, 77, -37, -37, -37, -37, -37, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 46, 41, 0, 39, 0, 51, 0
, 0, 0, 49, 47, 0, 0, 0, 40, 43, 0, 0, 0, 42, 0, 0, 44, 0, 0, 0, 0
, 0, 0, 133, 0, 0, 0, 0, 0, 50, 0, 0, 48, 0, 0, 0, 0, 46, 41, 0, 39
, 0, 51, 0, 0, 0, 49, 47, 0, 0, 0, 40, 43, 0, 0, 0, 42, 0, 0, 44, 0
, 0, 0, 0, 0, 0, 134, 0, 0, 0, 0, 0, 50, 0, 0, 48, 0, 0, 0, 0, 46
, 41, 0, 39, 0, 51, 0, 0, 0, 49, 47, 0, 0, 0, 40, 43, 0, 0, 0, 42, 0
, 0, 44, 0, 0, 0, 0, 0, 0, 135, 0, 0, 0, 0, 0, 50, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 136, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 48, 0, 0, 0, 0, 46, 41, 0, 39, 0, 51, 0, 0, 0, 49, 47, 0, 0, 0, 40
, 43, 0, 0, 0, 42, 0, 0, 44, 0, 0, 0, 0, 0, 137, 138, 0, 0, 0, 0, 0
, 50, 0, -26, -26, -26, 0, -26, -26, -26, -26, -26, -26, -26, -26, 78, -26, 0, -26, -26, -26
, -26, -26, -26, -26, -26, -26, -26, -26, -26, -26, -26, -26, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, -27, -27, -27, 0, -27, -27, -27, -27, -27, -27, -27, -27, 78, -27, 0
, -27, -27, -27, -27, -27, -27, -27, -27, -27, -27, -27, -27, -27, -27, -27, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, -29, -29, -29, 0, -29, -29, 75, -29, 72, -29, -29, -29
, 78, -29, 0, -29, -29, -29, -29, -29, -29, -29, -29, -29, -29, -29, -29, -29, -29, -29, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -30, -30, -30, 0, -30, -30, 75, -30, 72
, -30, -30, -30, 78, -30, 0, -30, -30, -30, -30, -30, -30, -30, -30, -30, -30, -30, -30, -30, -30
, -30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -28, -28, -28, 0, -28, -28
, -28, -28, 72, -28, -28, -28, 78, -28, 0, -28, -28, -28, -28, -28, -28, -28, -28, -28, -28, -28
, -28, -28, -28, -28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, -31, -31
, 0, 74, -31, 75, -31, 72, -31, -31, -31, 78, -31, 0, -31, -31, -31, -31, -31, -31, -31, -31
, -31, -31, -31, -31, -31, -31, -31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 73, -32, -32, 0, 74, -32, 75, -32, 72, -32, -32, -32, 78, -32, 0, -32, -32, -32, -32, -32
, -32, -32, -32, 76, -32, -32, -32, -32, -32, -32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, -24, -24, -24, 0, -24, -24, -24, -24, -24, -24, -24, -24, -24, -24, 0, -24, -24
, -24, -24, -24, -24, -24, -24, -24, -24, -24, -24, -24, -24, -24, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 46, 41, 0, 39, 0, 51, 0, 0
, 0, 49, 47, 0, 0, 0, 40, 43, 0, 0, 0, 42, 0, 0, 44, 0, 0, 0, 0, 0
, 0, 139, 0, 0, 0, 0, 0, 50, 0, -21, -21, -21, 0, -21, -21, -21, -21, -21, -21, -21
, -21, -21, -21, 0, -21, -21, -21, -21, -21, -21, -21, -21, -21, -21, -21, -21, -21, -21, -21, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -40, -40, -40, 0, -40, -40, -40, -40
, -40, -40, -40, -40, -40, -40, 0, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40
, -40, -40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 140, 0, 0
, 0, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -35, -35
, -35, 0, -35, -35, -35, -35, -35, -35, -35, -35, -35, -35, 0, -35, -35, -35, -35, -35, -35, -35
, -35, -35, -35, -35, -35, -35, -35, -35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 48, 0, 0, 0, 0, 46, 41, 0, 39, 0, 51, 0, 0, 0, 49, 47, 0, 0
, 0, 40, 43, 0, 0, 0, 42, 0, 0, 44, 0, 0, 0, 0, 0, 0, 141, 0, 0, 0
, 0, 0, 50, 0, 0, 48, 0, 0, 0, 0, 46, 41, 0, 39, 0, 51, 0, 0, 0, 49
, 47, 0, 0, 0, 40, 43, 0, 0, 0, 42, 0, 0, 44, 0, 0, 0, 0, 0, 0, 142
, 0, 0, 0, 0, 0, 50, 0, 0, 0, -17, 0, 0, 0, 0, 0, 0, 0, -17, 0, 0
, 0, 0, 0, 0, -17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 143, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 24, 0, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 0, 0, 0
, 74, 0, 75, 0, 72, 0, 0, 0, 78, 0, 0, 0, 0, -7, 0, 0, 0, 0, 0, 76
, 77, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73
, 0, 0, 0, 74, 0, 75, 0, 72, 0, 0, 0, 78, 0, 0, 0, 0, -5, 0, 0, 0
, 0, 0, 76, 77, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 73, 0, 0, 0, 74, 0, 75, 0, 72, 0, 0, 0, 78, 0, 0, 0, 0, -6
, 0, 0, 0, 0, 0, 76, 77, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 73, 0, 0, 0, 74, 0, 75, 0, 72, 0, 0, 0, 78, 0, 0
, 0, 0, -4, 0, 0, 0, 0, 0, 76, 77, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 73, 0, 0, 0, 74, 0, 75, 0, 72, 0, 0, 0
, 78, 0, 0, 0, 0, -8, 0, 0, 0, 0, 0, 76, 77, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 0, 0, 0, 74, 0, 75, 0, 72
, 0, 0, 0, 78, 0, 0, 0, 0, -9, 0, 0, 0, 0, 0, 76, 77, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 0, 0, 0, 74, 0
, 75, 0, 72, 0, 0, 0, 78, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 76, 77, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, -36, 0
, 0, 74, 0, 75, -36, 72, -36, 0, -36, 78, 0, 0, -36, -36, 0, 0, 0, -36, -36, 0
, 76, 77, -36, 0, 0, -36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 73, 0, 0, 0, 74, 0, 75, 0, 72, 0, 0, 0, 78, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 76, 77, 0, 0, 145, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 73, 0, 0, 0, 74, 0, 75, 0, 72, 0, 0, 0, 78, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 76, 77, 0, 0, 0, 0, 146, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 73, 0, 0, 0, 74, 0, 75, 0, 72, 0, -47, 0, 78, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 76, 77, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 147, 0, 0, 0, 0, 0, 148, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 46, 41
, 0, 39, 0, 51, 0, 0, 0, 49, 47, 0, 0, 0, 40, 43, 0, 0, 0, 42, 0, 0
, 44, 0, 0, 0, 0, 0, 0, 149, 0, 0, 0, 0, 0, 50, 0, 73, -52, 0, 0, 74
, 0, 75, -52, 72, -52, 0, -52, 78, 0, 0, -52, -52, 0, 0, 0, -52, -52, 0, 76, 77
, -52, 0, 0, -52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 0
, 0, 0, 74, 0, 75, 0, 72, 0, 0, 0, 78, 0, 0, 0, 0, 0, 0, 150, 0, 0
, 0, 76, 77, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, -20, -20, -20, 0, -20, -20, -20, -20, -20, -20, -20, -20, -20, -20, 0, -20, -20, -20, -20
, -20, -20, -20, -20, -20, -20, -20, -20, -20, -20, -20, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 73, 0, -34, 0, 74, -34, 75, 0, 72, 0, -34, 0, 78, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 76, 77, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 73, 0, 0, 0, 74, 0, 75, 0, 72, 0, 0, 0, 78
, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 76, 77, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0
, 0, 0, 151, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -16, 0, 0, 0, 0
, 0, 0, 0, -16, 0, 0, 0, 0, 0, 0, -16, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 152, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 48, 0, 0, 0, 0, 46, 41, 0, 39, 0, 51, 0, 0, 0, 49, 47, 0, 0, 0, 40
, 43, 0, 0, 0, 42, 0, 0, 44, 0, 0, 0, 0, 0, 0, 153, 0, 0, 0, 0, 0
, 50, 0, 0, 48, 0, 0, 0, 0, 46, 41, 0, 39, 0, 51, 0, 0, 0, 49, 47, 0
, 0, 0, 40, 43, 0, 0, 0, 42, 0, 0, 44, 0, 0, 0, 0, 0, 0, 154, 0, 0
, 0, 0, 0, 50, 0, 0, 48, 0, 0, 0, 0, 46, 41, 0, 39, 0, 51, 0, 0, 0
, 49, 47, 0, 0, 0, 40, 43, 0, 0, 0, 42, 0, 0, 44, 0, 0, 0, 0, 0, 0
, 155, 0, 0, 0, 0, 0, 50, 0, 73, -38, -38, 0, 74, -38, 75, -38, 72, -38, -38, -38
, 78, -38, 0, -38, -38, -38, -38, -38, -38, -38, -38, 76, 77, -38, -38, -38, -38, -38, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 46, 41, 0
, 39, 0, 51, 0, 0, 0, 49, 47, 0, 0, 0, 40, 43, 0, 0, 0, 42, 0, 0, 44
, 0, 0, 0, 0, 0, 0, 156, 0, 0, 0, 0, 0, 50, 0, 0, 0, -18, 0, 0, 0
, 0, 0, 0, 0, -18, 0, 0, 0, 0, 0, 0, -18, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0
, 0, 0, 0, 46, 41, 0, 39, 0, 51, 0, 0, 0, 49, 47, 0, 0, 0, 40, 43, 0
, 0, 0, 42, 0, 0, 44, 0, 0, 0, 0, 0, 0, 157, 0, 0, 0, 0, 0, 50, 0
, 73, 0, 0, 0, 74, 0, 75, 0, 72, 0, 0, 0, 78, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 76, 77, 0, 0, 158, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 73, 0, 0, 0, 74, 0, 75, 0, 72, 0, -48, 0, 78, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 76, 77, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 73, 0, 0, 0, 74, 0, 75, 0, 72, 0, 0, 0, 78, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 76, 77, 0, -49, 0, 0, -49, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, -22, -22, 0, 74, -22, 75, -22, 72, -22, -22
, -22, 78, 159, 0, -22, -22, -22, -22, -22, -22, -22, -22, 76, 77, -22, -22, -22, -22, -22, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 0, 160, 0, 74, 0, 75, 0
, 72, 0, 0, 0, 78, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 76, 77, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 161, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -23, -23
, -23, 0, -23, -23, -23, -23, -23, -23, -23, -23, -23, -23, 0, -23, -23, -23, -23, -23, -23, -23
, -23, -23, -23, -23, -23, -23, -23, -23, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, -50, -50, -50, 0, -50, -50, -50, -50, -50, -50, -50, -50, -50, -50, 0, -50, -50, -50, -50
, -50, -50, -50, -50, -50, -50, -50, -50, -50, -50, -50, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 46, 41, 0, 39, 0, 51, 0, 0, 0, 49
, 47, 0, 0, 0, 40, 43, 0, 0, 0, 42, 0, 0, 44, 0, 0, 0, 0, 0, 0, 162
, 0, 0, 0, 0, 0, 50, 0, 73, 0, 163, 0, 74, 0, 75, 0, 72, 0, 0, 0, 78
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 76, 77, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -51, -51, -51, 0, -51, -51, -51, -51, -51, -51
, -51, -51, -51, -51, 0, -51, -51, -51, -51, -51, -51, -51, -51, -51, -51, -51, -51, -51, -51, -51
] 