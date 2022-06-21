Module format

use UTF8

use bits

use standard

use seq.byte

use stack.word

use seq.seq.char

use stack.seq.word

Function getheader(s:seq.word)seq.word
let istype = subseq(s, 1, 3) = "Export type:"
let start = 0
let startname = -1
let extendname = -2
let findend = -3
let extendtype = -4
let extendtype2 = -5
let incomment = -6
let unknown = -7
let theend = 
 for state = 0, idx = 1, ele ∈ s
 while state ≤ 0
 do next(if state > 0 then state
 else if state = start then startname
 else if state = startname then extendname
 else if state = extendname then
  if ele ∈ ":."then startname
  else if istype then idx - 1
  else if ele ∈ "("then findend else extendtype
 else if state = findend then if ele ∈ ")"then extendtype2 else findend
 else if state = extendtype then
  if ele ∈ "."then extendtype2
  else if ele ∈ "//"then incomment else{done}idx - 1
 else if state = extendtype2 then extendtype
 else if state = incomment then if ele ∈ "//"then extendtype else incomment
 else unknown
 , idx + 1
 )
 /for(if state < 1 then length.s else state /if)
if istype then
 let tt = subseq(s, 4, theend)
 subseq(s, 1, theend) + "(" + tt + ")" + tt + "stub"
else subseq(s, 1, theend) + "stub"

type pnpstate is lastbreak:int, result:seq.word, matchthis:word, instring:boolean

Function prettynoparse(s:seq.word)seq.word
{format function without first parsing it}
result.for acc = pnpstate(0, "", "//"_1, false), @e ∈ s do advancepnp(acc, @e)/for(acc)

function advancepnp(state:pnpstate, this:word)pnpstate
let lastbreak = lastbreak.state
let result = result.state
let matchthis = matchthis.state
let instring = instring.state
let newinstring = if instring then this ≠ matchthis else this = "//"_1 ∨ this = dq_1
let newmatchthis = if instring then matchthis else this
let c = 
 if newinstring then 0
 else if this ∈ "if then else let assert function Function type"then 1
 else if this ∈ "report"then 2
 else if lastbreak > 20 ∧ this ∈ ")]" ∨ lastbreak > 40 ∧ this ∈ ", "then 3
 else if lastbreak > 20 ∧ this ∈ "["then 4 else 5
let newresult = 
 if instring then
  if this = matchthis then result + this + " />"else result + this
 else if c = 0 then
  result
  + if this ∈ dq then" /< literal"else" /br  /< comment"/if
  + this
 else if c = 1 then
  if lastbreak > 20 then result + " /br"else result /if
  + " /keyword"
  + this
 else if c = 2 then result + " /keyword" + this
 else if c = 3 then result + this + " /br"
 else if c = 4 then result + " /br" + this else result + this
let newlastbreak = if c ∈ [3, 4]then 0 else lastbreak + 1
pnpstate(newlastbreak, newresult, newmatchthis, newinstring)

_____________________________

Function HTMLformat(output:seq.word)UTF8 processpara(emptyUTF8, output)

Function htmlheader seq.word
{the format of the meta tag is carefully crafted to get math unicode characters to display correctly}
"<!doctype html> <meta charset="
+ dq."UTF-8"
+ ">"
+ "<style > <!--span.avoidwrap{display:inline-block ;}"
+ "span.keyword{color:blue ;}span.keywords{color:blue ;}"
+ "span.literal{color:red ;}span.comment{color:green ;}"
+ "span.block{padding:0px 0px 0px 0px ; margin:0px 0px 0px 20px ; display:block ;}"
+ {"form{margin:0px ;}html, body{margin:0 ; padding:0 ; height:100% ;}"+".container{margin:0 ; padding:0 ; height:
100% ; display:-webkit-flex ; display:flex ; flex-direction:column ;}"+".floating-menu{margin:0 ; padding:0 ; background 
:yellowgreen ; padding:0.5em ;}"+".content{margin:0 ; padding:0.5em ;-webkit-flex:1 1 auto ; flex:1 1 auto ; overflow 
:auto ; height:0 ; min-height:0 ;"}}
"--> </style>"
+ EOL

___________________

function +(result:UTF8, toadd:seq.word)UTF8
if isempty.toadd then result
else
 let nospace = 
  isempty.toseqbyte.result
  ∨ toint.last.toseqbyte.result ∈ [10, 32, 34, 40, 41, 43, 45, 46, 58, 61, 91, 93, 94, 95, 123, 125]
 result + toUTF8(toadd, empty:seq.seq.char, nospace)

Function processpara(x:UTF8, a:seq.word)UTF8
let none = merge."+NONE"
let match = merge."+MaTcH"
let pendingbreak = merge."+pendingBreak"
for result = x, stk = empty:stack.seq.word, last = none, this ∈ a + space do
 if last = match then
  if this = " /<"_1 then next(result + [this], push(stk, [this]), match)
  else if this = " />"_1 then
   if not.isempty.stk ∧ top.stk = " /<"then next(result + [this], pop.stk, match)
   else next(result, stk, none)
  else next(result + [this], stk, last)
 else if last = none then next(result, stk, this)
 else if last = " /keyword"_1 then
  next(result + ("<span class=keyword>" + this + "</span>"), stk, none)
 else if last = " /em"_1 then next(result + ("<em>" + this + "</em>"), stk, none)
 else if last = " /strong"_1 then
  next(result + ("<strong>" + this + "</strong>"), stk, none)
 else if last = " /p"_1 then next(result + char.10 + "<p>", stk, this)
 else if last = " /row"_1 then
  if not.isempty.stk ∧ top.stk = "</caption>"then
   next(result + char.10 + (top.stk + "<tr><td>"), pop.stk, this)
  else next(result + char.10 + "<tr><td>", stk, this)
 else if last = " /cell"_1 then next(result + char.10 + "<td>", stk, this)
 else if last = " /br"_1 then
  if this ≠ " /<"_1 then next(result + char.10 + "<br>" + char.32, stk, this)
  else next(result, stk, pendingbreak)
 else if last = " /<"_1 ∨ last = pendingbreak then
  if this = "block"_1 then
   {if break is just before block suppress break}
   next(result + ("<span class=block>" + space), push(stk, "</span>"), none)
  else
   let pb = 
    if last = pendingbreak then result + char.10 + ("<br>" + space)else result
   if this = "noformat"_1 then next(result, stk, match)
   else if this = "/section"_1 then
    next(pb + char.10 + ("<h2>" + space), push(stk, "</h2>"), none)
   else if this = "table"_1 then
    next(pb + ("<table>" + space + "<caption>")
    , push(push(stk, "</table>"), "</caption>")
    , none
    )
   else
    next(pb + ("<span class=" + this + ">"), push(stk, "</span>"), none)
 else if last = " />"_1 ∧ not.isempty.stk then
  let toadd = top.stk + space
  next(result + toadd
  , pop.stk
  , if this = first." /br"then none else this
  )
 else
  let nospace = 
   isempty.toseqbyte.result
   ∨ toint.last.toseqbyte.result ∈ [10, 32, 34, 40, 41, 43, 45, 46, 58, 61, 91, 93, 94, 95, 123, 125]
  next(result + toUTF8([last], HTMLformat, nospace), stk, this)
/for(if last = none then result else result + [last]/if)

Function textformat(a:seq.word)UTF8
let none = merge."+NONE"
let match = merge."+MaTcH"
let pendingbreak = merge."+pendingBreak"
for needsLF = false, result = emptyUTF8, stk = empty:stack.word, last = none, this ∈ a + space do
 {assert this /ne first.", "report"x"+last+if needsLF then"LF"else""}
 if last = match then
  if this = " /<"_1 then next(needsLF, result + [this], push(stk, this), match)
  else if this = " />"_1 then
   if not.isempty.stk ∧ top.stk = " /<"_1 then next(needsLF, result + [this], pop.stk, match)
   else next(needsLF, result, stk, none)
  else next(needsLF, result + [this], stk, last)
 else if last = none then next(needsLF, result, stk, this)
 else if last = " /br"_1 then
  if this = " /br"_1 then next(needsLF, result, stk, this)
  else next(needsLF, result + char.10 + toseq.stk, stk, this)
 else if last = " /<"_1 then
  if this = "block"_1 then
   if needsLF then next(needsLF, result + char.10 + char.32 + toseq.stk, push(stk, space), none)
   else next(needsLF, result, push(stk, space), none)
  else if this = "noformat"_1 then next(needsLF, result, stk, match)
  else next(needsLF, result, push(stk, space), none)
 else if last = " />"_1 ∧ not.isempty.stk then next(needsLF, result, pop.stk, this)
 else if last ∈ " /keyword  /em  /strong"then next(needsLF, result, stk, this)
 else if last = " /p"_1 then next(true, result + char.10 + char.10, stk, this)
 else if last = space then next(needsLF, result + [space], stk, this)
 else next(true, result + [last], stk, this)
/for(if last = none then result else result + [last]/if)

Export type:UTF8

Export towords(UTF8)seq.word

function chrs(s:seq.word)seq.char decodeword.s_1

function chrs(i:int)seq.char[char.i]

Function HTMLformat seq.seq.char
[chrs.1
, chrs.2
, chrs.3
, chrs.4
, chrs.5
, chrs.6
, chrs.7
, chrs.8
, chrs.9
, chrs.10
, chrs.11
, chrs.12
, chrs.13
, chrs.14
, chrs.15
, chrs.16
, chrs.17
, chrs.18
, chrs.19
, chrs.20
, chrs.21
, chrs.22
, chrs.23
, chrs.24
, chrs.25
, chrs.26
, chrs.27
, chrs.28
, chrs.29
, chrs.30
, chrs.31
, chrs.32
, chrs."!"
, chrs.dq
, chrs."#"
, chrs."$"
, chrs."%"
, chrs."&amp;"
, chrs."'"
, chrs."("
, chrs.")"
, chrs."*"
, chrs."+"
, chrs.", "
, chrs."-"
, chrs."."
, chrs."/"
, chrs."0"
, chrs."1"
, chrs."2"
, chrs."3"
, chrs."4"
, chrs."5"
, chrs."6"
, chrs."7"
, chrs."8"
, chrs."9"
, chrs.":"
, chrs.";"
, chrs."&lt;"
]

Function perserveFormat seq.seq.char
[chrs.1
, chrs.2
, chrs.3
, chrs.4
, chrs.5
, chrs.6
, chrs.7
, chrs.8
, chrs.9
, [char.92, char.48, char.49, char.50]
, chrs.11
, chrs.12
, chrs.13
, chrs.14
, chrs.15
, chrs.16
, chrs.17
, chrs.18
, chrs.19
, chrs.20
, chrs.21
, chrs.22
, chrs.23
, chrs.24
, chrs.25
, chrs.26
, chrs.27
, chrs.28
, chrs.29
, chrs.30
, chrs.31
, [char.92, char.48, char.52, char.48]
, chrs."!"
, chrs.dq
, chrs."#"
, chrs."$"
, chrs."%"
, chrs."&"
, chrs."'"
, [char.92, char.48, char.53, char.48]
, [char.92, char.48, char.53, char.49]
, chrs."*"
, [char.92, char.48, char.53, char.51]
, [char.92, char.48, char.53, char.52]
, [char.92, char.48, char.53, char.53]
, [char.92, char.48, char.53, char.54]
, chrs."/"
, chrs."0"
, chrs."1"
, chrs."2"
, chrs."3"
, chrs."4"
, chrs."5"
, chrs."6"
, chrs."7"
, chrs."8"
, chrs."9"
, [char.92, char.48, char.55, char.50]
, chrs.";"
, chrs."<"
, [char.92, char.48, char.55, char.53]
, chrs.">"
, chrs."?"
, chrs."@"
, chrs."A"
, chrs."B"
, chrs."C"
, chrs."D"
, chrs."E"
, chrs."F"
, chrs."G"
, chrs."H"
, chrs."I"
, chrs."J"
, chrs."K"
, chrs."L"
, chrs."M"
, chrs."N"
, chrs."O"
, chrs."P"
, chrs."Q"
, chrs."R"
, chrs."S"
, chrs."T"
, chrs."U"
, chrs."V"
, chrs."W"
, chrs."X"
, chrs."Y"
, chrs."Z"
, [char.92, char.49, char.51, char.51]
, chrs."\"
, [char.92, char.49, char.51, char.53]
, [char.92, char.49, char.51, char.54]
, [char.92, char.49, char.51, char.55]
, chrs."`"
, chrs."a"
, chrs."b"
, chrs."c"
, chrs."d"
, chrs."e"
, chrs."f"
, chrs."g"
, chrs."h"
, chrs."i"
, chrs."j"
, chrs."k"
, chrs."l"
, chrs."m"
, chrs."n"
, chrs."o"
, chrs."p"
, chrs."q"
, chrs."r"
, chrs."s"
, chrs."t"
, chrs."u"
, chrs."v"
, chrs."w"
, chrs."x"
, chrs."y"
, chrs."z"
, [char.92, char.49, char.55, char.51]
, chrs."|"
, [char.92, char.49, char.55, char.53]
, chrs."~"
, chrs.""
] 