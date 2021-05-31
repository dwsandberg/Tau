Module format

use UTF8

use bits

use standard

use outstream.UTF8

use seq.byte

use set.int

use stack.word

use seq.seq.word

use stack.seq.word

function changestate(state:int, ele:word, idx:int, early:boolean)int
let start = 0
let startname =-1
let extendname =-2
let findend =-3
let extendtype =-4
let extendtype2 =-5
let incomment =-6
let unknown =-7
 if state > 0 then state
 else if state = start then startname
 else if state = startname then extendname
 else if state = extendname then
  if ele ∈ ":."then startname
  else if early then idx - 1 else if ele ∈ "("then findend else extendtype
 else if state = findend then if ele ∈ ")"then extendtype2 else findend
 else if state = extendtype then
  if ele ∈ "."then extendtype2
  else if ele ∈ "//"then incomment else { done }idx - 1
 else if state = extendtype2 then extendtype
 else if state = incomment then if ele ∈ "//"then extendtype else incomment else unknown

Function getheader(s:seq.word)seq.word
let istype = subseq(s, 1, 3) = "Export type:"
let t = for state = 0, idx = 1, ele = s while state ≤ 0 do next(changestate(state, ele, idx, istype), idx + 1)/for(state)
let theend = if t < 1 then length.s else t
 if istype then
 let tt = subseq(s, 4, theend)
 subseq(s, 1, theend) + "(" + tt + ")" + tt + "stub"
 else subseq(s, 1, theend) + "stub"

Function escapeformat(s:seq.word)seq.word
 for acc ="", c = s do
  acc
  + if c ∈ " /<  /br  /p  /row"then
   if length.s > 20 then merge.[ encodeword.[ char.10], c]else merge.[ space, c]
  else if c ∈ " /keyword  />  /em  /strong  /cell"then merge.[ space, c]else c
 /for(acc)

Function htmlheader seq.word { the format of the meta tag is carefully crafted to get math unicode characters to display correctly }"<meta"
+ merge.' http-equiv ="Content-Type"'
+ ' content ="text/html; '
+ merge."charset = utf-8"
+ '"> <style type ="text/css"> <!--span.avoidwrap { display:inline-block ; } '
+ ' span.keyword { color:blue ; } span.keywords { color:blue ; } '
+ ' span.literal { color:red ; } span.comment { color:green ; } '
+ ' span.block { padding:0px 0px 0px 0px ; margin:0px 0px 0px 20px ; display:block ; } '
+ ' form { margin:0px ; } html, body { margin:0 ; padding:0 ; height:100% ; }.container { margin:0 ; padding:0 ; height:100% ; display:-webkit-flex ; display:flex ; flex-direction:column ; }.floating-menu { margin:0 ; padding:0 ; background:yellowgreen ; padding:0.5em ; }.content { margin:0 ; padding:0.5em ;-webkit-flex:1 1 auto ; flex:1 1 auto ; overflow:auto ; height:0 ; min-height:0 ; }--> </style> '
+ EOL

type pnpstate is lastbreak:int, result:seq.word, matchthis:word, instring:boolean

Function prettynoparse(s:seq.word)seq.word
 { format function without first parsing it }
 result.for acc = pnpstate(0,"","//"_1, false), @e = s do advancepnp(acc, @e)/for(acc)

function advancepnp(state:pnpstate, this:word)pnpstate
let lastbreak = lastbreak.state
let result = result.state
let matchthis = matchthis.state
let instring = instring.state
let newinstring = if instring then this ≠ matchthis
else
 this = "//"_1 ∨ this = "'"_1 ∨ this = '"'_1
let newmatchthis = if instring then matchthis else this
let c = if newinstring then 0
else if this ∈ "if then else let assert function Function type"then 1
else if this ∈ "report"then 2
else if lastbreak > 20 ∧ this ∈ ")]"
∨ lastbreak > 40 ∧ this ∈ ","then
 3
else if lastbreak > 20 ∧ this ∈ "["then 4 else 5
let newresult = if instring then
 if this = matchthis then result + this + " />"else result + this
else if c = 0 then
 result
 + if this ∈ ('"' + "'")then" /< literal"else" /br  /< comment"/if
 + this
else if c = 1 then
 if lastbreak > 20 then result + " /br"else result /if + " /keyword" + this
else if c = 2 then result + " /keyword" + this
else if c = 3 then result + this + " /br"
else if c = 4 then result + " /br" + this else result + this
let newlastbreak = if c ∈ [ 3, 4]then 0 else lastbreak + 1
 pnpstate(newlastbreak, newresult, newmatchthis, newinstring)

_____________________________

Function toUTF8bytes(output:seq.word)seq.byte toseqbyte.processpara(emptyUTF8," /< noformat" + htmlheader + " />" + output)

Function toUTF8textbytes(output:seq.word)seq.byte toseqbyte.processtotext(emptyUTF8, output) 