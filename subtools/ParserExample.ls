Module ParserExample

To get started building a new parser the following function will work to produce tables for a new parser

use file

use standard

use seq.stkele

use stack.stkele

type ATTR is val:int

type stkele is stateno:int, attribute:ATTR

type reduction is toseq:seq.stkele

function forward(stk:ATTR, token:ATTR) ATTR token

function _(r:reduction, n:int) ATTR attribute.(toseq.r)_n

Function sampleparser(input:seq.file, data:seq.word, o:seq.word) seq.file
[file(o, "Value of the sum of $(data) is $(sampleparse.data)")]

* The /keyword sampleparser command is a very simple example of a parser generated using the /keyword
genLR1 parser. It will add up a sequence of integers. For exmple" sampleparser data = 3 4 5" will
give the result of" Value of the sum of 3 4 5 is 12".The grammar was produced with" LR1+tools ParserExample
.ls flags = codeonly"

function sampleparse(input:seq.word) int
for lrpart = push(empty:stack.stkele, stkele(startstate, ATTR.0))
, idx = 1
, this ∈ input + "#"
while stateno.top.lrpart ≠ finalstate
do
 {lexical analysis is done here}
 {Assume the input is only integers}
 let tokenno = 
  if findindex(tokenlist, this) > length.tokenlist then findindex(tokenlist, "I"_1)
  else findindex(tokenlist, "#"_1)
 let attribute = ATTR.if this ∈ {end marked} "#" then 0 else toint.this
 next(step(lrpart, input, attribute, tokenno, idx), idx + 1)
/for (val.attribute.undertop(lrpart, 1))

function step(stk:stack.stkele, input:seq.word, attrib:ATTR, tokenno:int, place:int) stack.stkele
let stateno = stateno.top.stk
let actioncode = actiontable_(tokenno + length.tokenlist * stateno)
if actioncode > 0 then
 if stateno = finalstate then stk
 else push(stk, stkele(actioncode, forward(attribute.top.stk, attrib)))
else
 assert actioncode < 0 report "ERROR"
 let ruleno = -actioncode
 let rulelen = rulelength_ruleno
 let newstk = pop(stk, rulelen)
 let newstateno = actiontable_(leftside_ruleno + length.tokenlist * stateno.top.newstk)
 let newstkele = stkele(newstateno, action(ruleno, input, place, reduction.top(stk, rulelen)))
 step(push(newstk, newstkele), input, attrib, tokenno, place)

-----

This part is generated with LR1 command (with the exception of the action header.)

function action(ruleno:int, input:seq.word, place:int, R:reduction) ATTR
{Alphabet I # F G}
if ruleno = {G F #} 1 then R_1
else if ruleno = {F F I} 2 then
 {The left side of the grammar rule is F and the right side is F I} ATTR(val.R_1 + val.R_2)
else if ruleno = {F I} 3 then R_1
else
 {ruleno}
 assert false report "invalid rule number" + toword.ruleno
 R_1

function rulelength seq.int [2, 2, 1]

function leftside seq.int [4, 3, 3]

function tokenlist seq.word "I # F G"

function startstate int 1

function finalstate int 4

function actiontable seq.int
[0, 0, 0, 0, 3, 0, 2, 0, 5, 4, 0, 0,-3,-3, 0, 0, 0, 0, 0, 0,-2,-2] 