Module newPretty

use PEGrules

use UTF8

use prettyAttribute

use otherseq.prettyR

use standard

use otherseq.word

use set.seq.word

Function %(a:attribute) seq.word %.parts.a

function %(p:prettyR) seq.word "{^(prec.p)}^(text.p)"

Export escapeformat(in:seq.word) seq.word {From prettyAttribute}

Function pretty(p:seq.word) seq.word
let r = parse(p, mytable, toAttribute."", true)
let out = text.1_parts.result.r,
if success.r then out else "Fail^(p)"

Function prettyNoChange(p:seq.word) seq.word
let r = parse(p, mytable, toAttribute."", false)
let out = text.1_parts.result.r,
if success.r then out else "Fail^(p)"

function binary2(a:attribute, b:attribute, op:seq.word) attribute
if isempty.text.1_parts.b then a else attribute(parts.a + parts.b)

function binary(a:attribute, b:attribute, op:seq.word) attribute
let tmp = if isempty.text.1_parts.a then empty:seq.prettyR else parts.a,
attribute(tmp + prettyR(-1, width.op, op) + parts.b)

function checkfirstdigit(chars:seq.char) boolean
let i = if n.chars > 1 ∧ 1_chars = char1."-" then 2 else 1,
between(toint.i_chars, 48, 57)

function unaryMinus(change:boolean, bin:attribute) attribute
let b = if change ∧ prec.1_parts.bin ≤ 2 then removeparen.bin else bin,
attribute.prettyR(2, 1 + width1.b, "-^(text1.b)")

function unaryExp(change:boolean, kind:int, a:attribute, b:attribute) attribute
if kind = 2 then
 if checkfirstdigit.decodeword.1_text1.a then
 attribute.prettyR(0, width1.a + width1.b, text1.a + "." + text1.b)
 else if change then
 funccall(change, a, b, toAttribute."")
 else attribute.prettyR(2, width1.a + width1.b, text1.a + "." + text1.b)
else
 let ce = CommentExp([prettyR(0, 2, "{")] + parts.a + prettyR(0, 2, "}")),
 attribute.
  if subseq(text1.b, 1, 2) = "<* block" then
   let c = mergelist(2, ce),
   prettyR(
    prec.1_parts.b
    , 10000
    , "<* block^(text1.c)
     /br^(text1.b << 2)"
   )
  else 1_parts.mergelist(prec.1_parts.b, ce + parts.b)

function mergebinary(change:boolean, prec:int, a0:attribute, b:attribute) attribute
let a1 = 1_parts.a0
let a2 =
 if change ∧ prec.a1 ≤ prec ∧ 1^text.a1 ∈ ") *>" then
  let txt = if prec = 11 then removeclose.text.a1 else removeparen.text.a1,
  [prettyR(prec.a1, width.txt, txt)]
 else parts.a0
,
if n.parts.b = 1 ∧ isempty.text.1_parts.b then
attribute.a2
else
 let aa =
  if prec = 1 ∧ prec.1_a2 = 1 then
  [prettyR(0, width.1_a2 + 2, "(^(text.1_a2))")]
  else a2
 for op = true, binary = "", acc = aa, e ∈ parts.b
 do
  if op then
   let t = text.e,
   next(false, if t ∈ [",", ".", "_", "^"] then t else "/sp^(t) /sp", acc)
  else
   let bb =
    if change ∧ prec.e < prec ∧ 1^text.e ∈ ") *>" then
     let txt = if binary = "," then removeclose.text.e else removeparen.text.e,
     prettyR(prec.e, width.txt, txt)
    else e
   ,
   next(true, binary, acc + prettyR(prec, width.binary + width.bb, binary + text.bb))
 ,
 mergelist(prec, acc)

Function sortuse(b:seq.seq.word, prefix:seq.word) seq.seq.word
let a = for a = empty:seq.seq.word, u ∈ b do a + reverse.u, a
for acc = empty:seq.seq.word, @e ∈ alphasort.toseq.asset.a do acc + (prefix + reverse.@e),
acc

function combine(change:boolean, a:seq.prettyR, b:seq.prettyR, E:attribute) attribute
if isempty.b ∧ isempty.a then
E
else if not.change then
let parts = a + b + parts.E, mergelist(if prec.1_parts = 10 then 10 else 11, parts)
else
 let tmp = removeparen.text1.E
 let e = if tmp = text1.E then 1_parts.E else prettyR(0, width.tmp, tmp),
  if not(n.b = 1 ∧ isempty.text.1_b) then
   let parts = a + if isempty.text.1^b then b >> 1 else b,
   mergelist(if prec.1^parts = 10 then 10 else 11, parts >> 1 + addcomma.1^parts + e)
  else mergelist(11, a + e)

function addcomma(p:prettyR) prettyR
for i = 0, e ∈ reverse.text.p while e ∈ "<*" do i + 1,
if subseq(text.p, n.text.p - i - 2, n.text.p - i - 2) = "}" then
p
else prettyR(
 prec.p
 , width."," + width.p
 , subseq(text.p, 1, n.text.p - i) + "," + subseq(text.p, n.text.p - i + 1, n.text.p)
)

function removeblocks(in:prettyR) prettyR
let tmp = text.in
let tmp2 = removeblock.tmp,
if n.tmp > n.tmp2 then prettyR(prec.in, width.tmp2, tmp2) else in

function mergelist(prec:int, in:seq.prettyR) attribute
if n.in = 1 then
attribute.in
else
 let tmp = text.1_in
 let tmp2 = removeblock.tmp,
  if n.tmp > n.tmp2 then
  mergelist(prec, [prettyR(prec, width.tmp2, tmp2)] + in << 1)
  else
   let t =
    for width = 0, text = "", e ∈ in
    while width < maxwidth
    do next(width + width.e, text + text.e),
    prettyR(prec, width, text)
   ,
    if width.t < maxwidth then
    attribute.t
    else
     for text = text.1_in, e ∈ in << 1
     do
      if isempty.text.e then
      text
      else
       let i = matchR.text
       let blockIsLast = subseq(text, n.text - i + 1, n.text - i + 2) = "<* block",
        if blockIsLast ∨ subseq(text.e, 1, 2) = "<* block" then
        text + text.e
        else text + "/br" + text.e
     ,
     attribute.prettyR(prec, 10000, addblock.text)

function IfExp(change:boolean, prefix:seq.word, R:reduction) seq.prettyR
assert n.parts.2_R = 1 report "PROBLEM"
let adjust = width.prefix + 5
let cond = if change then removeclose.1_R else 1_R
let thenpart = parts.if change then removeclose.2_R else 2_R
let Then = if 1_text.1_thenpart ∈ "-" then "/keyword then /sp" else "/keyword then",
[prettyR(0, width1.cond + adjust, prefix + text1.cond + Then)] + thenpart

function fullIfExp(change:boolean, R:reduction) attribute
let keywordelse = if 1_text1.4_R ∈ "-" then "/keyword else /sp" else "/keyword else"
let prefix = if change then "(/keyword if" else "/keyword if"
let tmp =
 if change then
 let mid = removeclose.4_R, prettyR(9, 6 + width1.mid, keywordelse + text1.mid + ")")
 else prettyR(9, 5 + width1.4_R, keywordelse + text1.4_R)
,
mergelist(9, IfExp(change, prefix, R) + parts.3_R + tmp)

function LetExp(change:boolean, a:attribute, b:attribute, c:attribute) seq.prettyR
[prettyR(
 10
 , width1.a + width1.b + width1.c + 6
 , "/keyword let^(text1.a) =^(if change then let x = removeclose.text1.b, x + text1.c else text1.b + text1.c)"
)]

function AssertExp(change:boolean, a:attribute, b:attribute, c:attribute) seq.prettyR
{assert E report E comma?}
let assertpart = "/keyword assert^(if change then removeclose.text1.a else text1.a)"
let reportpart = "/keyword report^(if change then removeclose.text1.b else text1.b)",
if width1.a + width1.b + width1.c + 16 < maxwidth then
[prettyR(0, width1.a + width1.b + width1.c + 16, "^(assertpart)^(reportpart)^(text1.c)")]
else [prettyR(0, width1.a + 8, assertpart), prettyR(0, width1.b + 8, reportpart)] + parts.c

Function AccumExp(
 change:boolean
 , accum:attribute
 , value:attribute
 , op:seq.word
) attribute
let B = if change then removeparen.value else value,
attribute.prettyR(0, width1.accum + width1.B + 2, text1.accum + op + text1.B)

function forExp(
 accumList:attribute
 , While:attribute
 , body:attribute
 , change:boolean
) attribute
{merge accum expressions}
let accums =
 if n.parts.accumList = 1 then
 accumList
 else
  let bb = attribute(parts.accumList << 1),
  mergebinary(change, 11, attribute.1_parts.accumList, bb)
let whilepart =
 if isempty.text1.While then
 prettyR(0, 0, "")
 else
  let b = if change then removeparen.While else While,
  prettyR(0, 6 + width1.b, "/keyword while^(text1.b)")
let dopart = if change then removeclose.body else body
let totalwidth = width1.accums + width1.dopart + width.whilepart + 7,
attribute.
 if totalwidth < maxwidth then
 [prettyR(
  10
  , totalwidth
  , "/keyword for^(text1.accums + text.whilepart) /keyword do^(text1.dopart)"
 )]
 else
  attr("/keyword for", accums)
  + whilepart
  + prettyR(10, 3 + width1.dopart, "/keyword do^(text1.dopart)")

function brackets(change:boolean, prec:int, ain:attribute) attribute
let a = if change then removeparen.ain else ain,
attribute.prettyR(prec.1_parts.a, width1.a + 2, "(^(text1.a))")

function CommentExp(parts:seq.prettyR) seq.prettyR
for width = 0, acc = [escapeformat], p ∈ parts do next(width + width.p, acc + text.p),
addBlock([prettyR(0, width, acc + [escapeformat])], "comment")

function quote(R:reduction) attribute
let t = addBlock(
 [prettyR(0, 1, "/ldq" + escapeformat)]
 + parts.1_R
 + parts.2_R
 + prettyR(0, 2, [escapeformat] + dq)
 , "literal"
)
for width = 0, text = "", e ∈ t do next(width + width.e, text + text.e),
attribute.prettyR(0, width, text)

function fixname(s:seq.word, a:attribute) seq.prettyR
let name = text.1_parts.a
let name1 = if 1_name ∈ "+=_-^" then s + space + name else s + name
let widthname = width.name1
let widthlast = width.1^parts.a
let textlast = if 1^s ∈ ":" then {Export type:} "" else text.1^parts.a
for text = "", width = 0, text2 = "", p ∈ subseq(parts.a, 2, n.parts.a - 1)
do next(text + text.p, width + width.p, if isempty.text.p then text2 else text2 + text.p + "/br"),
if widthname + width + widthlast < maxwidth then
[prettyR(0, widthname + width + widthlast, "/keyword^(name1)^(text)^(textlast)")]
else
 [prettyR(0, width.name1, "/keyword^(name1)")]
 + prettyR(0, 10000, addblock(text2 >> 1))
 + 1^parts.a

function start(s:seq.word, a:attribute, b:attribute) attribute
let tmp = if s = "type" then parts.toAttribute."/keyword type^(text1.a) is" else fixname(s, a),
toAttribute.removeblock.text1.mergelist(11, tmp + parts.b)

function start(
 change:boolean
 , s:seq.word
 , a:attribute
 , b:attribute
 , c:attribute
) attribute
let txt = removeclose.removeblock.removeparen.text1.c
let newc = if txt = text1.c then 1_parts.c else prettyR(0, width.txt, txt),
toAttribute.removeblock.text1.combine(change, fixname(s, a), parts.b, attribute.newc)

Function strEsc(R:reduction) attribute
attribute(
 parts.0_R
 + prettyR(
  0
  , width1.1_R + width1.2_R + 4
  ,
   text1.1_R
   + "^"
   + "("
   + escapeformat
   + removeparen.text1.2_R
   + escapeformat
   + ")"
 )
)

function addBlock(s:seq.prettyR, kind:seq.word) seq.prettyR
if n.s = 1 then
[prettyR(0, width.1_s, "<*^(kind)^(text.1_s) *>")]
else [prettyR(0, 0, "<*^(kind)")] + s + prettyR(0, 0, "*>")

function slash word 1_"/"

function break word 1_"/br"

function row word 1_"/row"

function paragraph word 1_"/p"

function escape(R:reduction, i:int) attribute
let ith =
 i
 _"/br
  /p
  /row"
,
if n.parts.0_R = 1 ∧ isempty.text.1_parts.0_R ∧ n.parts.1_R = 1 then
 let t = 1_parts.1_R
 let w = if ith ∈ "/br" then 4 else if ith ∈ "/p" then 3 else 5,
 attribute.prettyR(0, w + width.t, text.t + [ith])
else attribute(
 parts.0_R
 + parts.1_R
 + prettyR(0, 10000, [escapeformat] + "/br" + [escapeformat] + ith)
)

function /All word 1_"All"

function funccall(change:boolean, name:attribute, b:attribute, c:attribute) attribute
let a = 1_parts.b
let aa =
 if change ∧ 1^text.a ∈ ") *>" then
 let txt = removeclose.text.a, prettyR(prec.a, width.a + n.txt - n.text.a, txt)
 else a
,
attribute.
 if n.parts.c = 1 ∧ isempty.text1.c then
  if n.parts.name = 0 then
  prettyR(0, width.aa + 4, "[/nosp^(text.aa)]")
  else if change ∧ n.text1.name = 1 ∧ prec.aa ≤ 2 then
  let new = "^(text1.name).^(text.aa)", prettyR(2, width.new, new)
  else if change ∧ prec.aa = 9 then
  prettyR(9, width1.name + 1 + width.aa, "(^(text1.name).^(text.aa))")
  else prettyR(0, width1.name + 2 + width.aa, "^(text1.name) /nosp (^(text.aa))")
 else
  let aa1 = removeblocks.aa
  for op = true, acc = text.aa1, blockacc = text.aa1, width = width.aa1, e ∈ parts.c
  do
   if op then
   next(false, acc, blockacc, width)
   else
    let bb0 =
     if change ∧ 1^text.e ∈ ") *>" then
     let txt = removeclose.text.e, prettyR(prec.e, width.txt, txt)
     else e
    let bb = if prec.e ≠ 10 then bb0 else prettyR(prec.e, width.bb0 + 2, "(^(text.bb0))")
    let text = blockacc
    let i = matchR.blockacc
    let blockIsLast = subseq(blockacc, n.blockacc - i + 1, n.blockacc - i + 2) = "<* block"
    let newblockacc = blockacc + if blockIsLast then ",^(text.bb)" else "/br,^(text.bb)",
    next(true, acc + "," + text.bb, newblockacc, width + width."," + width.bb)
  ,
   if n.parts.name = 0 then
    let totalwidth = width + 4,
     if width < maxwidth then
     prettyR(0, totalwidth, "[/nosp^(acc)]")
     else prettyR(0, 10000, "[/nosp^(addblock.blockacc)]")
   else
    let totalwidth = width + width1.name + 2,
     if width < maxwidth then
     prettyR(0, totalwidth, "^(text1.name) /nosp (^(acc))")
     else prettyR(0, totalwidth, "^(text1.name) /nosp (^(addblock.blockacc))")

function PEGgen(
 seqElementType:word
 , attributeType:attribute
 , runresultType:runresult
 , R:reduction
 , common:boolean
) seq.boolean
[
 "match2code carrot" = 1_"^"
 , "/ slash" = slash
 , "/ break" = break
 , "/ paragraph" = paragraph
 , "/ row" = row
 , "/ dq" = 1_dq
 , "/ any" = 1_"/1"
 , "S function Header Declare' E" = start(common, "function", 1_R, 2_R, 3_R)
 , "/ Function Header Declare' E" = start(common, "Function", 1_R, 2_R, 3_R)
 , "/ type Id is FPL Comment" = start("type", 1_R, attribute(parts.2_R + parts.3_R))
 , "/ Export type:Type Comment" = start("Export type:", 1_R, 2_R)
 , "/ Export Header Comment" = start("Export", 1_R, 2_R)
 , "/ Builtin Header Comment" = start("Builtin", 1_R, 2_R)
 , "/ builtin Header Comment" = start("builtin", 1_R, 2_R)
 , "/ unbound Header Comment" = start("unbound", 1_R, 2_R)
 , "String dq String' str2 dq" = quote.R
 , "* String' str2 carrot (E)" = strEsc.R
 ,
  "/ str2 carrot"
  = attribute(parts.0_R + prettyR(0, width1.1_R + 2, text1.1_R + "^"))
 , "/ str2 break" = escape(R, 1)
 , "/ str2 paragraph" = escape(R, 2)
 , "/ str2 row" = escape(R, 3)
 , "/ str2" = attribute(parts.0_R + parts.1_R)
 , "* str2 ! dq ! carrot ! row ! paragraph ! break any" = /All
 , "E Or" = 1_R
 , "* EL', E" = binary(0_R, 1_R, ",")
 , "Or And Or'" = mergebinary(common, 8, 1_R, 2_R)
 , "* Or' ∨ And" = binary(0_R, 1_R, "∨")
 , "/ /or And" = binary(0_R, 1_R, "∨")
 , "/ ⊻ And" = binary(0_R, 1_R, "⊻")
 , "And Compare And'" = mergebinary(common, 7, 1_R, 2_R)
 , "* And' ∧ Compare" = binary(0_R, 1_R, "∧")
 , "/ /and Compare" = binary(0_R, 1_R, "∧")
 , "Compare Sum Compare'" = mergebinary(common, 6, 1_R, 2_R)
 , "* Compare' = Sum" = binary(0_R, 1_R, "=")
 , "/ ≠ Sum" = binary(0_R, 1_R, "≠")
 , "/ > Sum" = binary(0_R, 1_R, ">")
 , "/ < Sum" = binary(0_R, 1_R, "<")
 , "/ >1 Sum" = binary(0_R, 1_R, ">1")
 , "/ >2 Sum" = binary(0_R, 1_R, ">2")
 , "/ ≥ Sum" = binary(0_R, 1_R, "≥")
 , "/ /ge Sum" = binary(0_R, 1_R, "≥")
 , "/ ≤ Sum" = binary(0_R, 1_R, "≤")
 , "/ /le Sum" = binary(0_R, 1_R, "≤")
 , "/ /ne Sum" = binary(0_R, 1_R, "≠")
 , "Sum Product Sum'" = mergebinary(common, 4, 1_R, 2_R)
 , "* Sum'-Product" = binary(0_R, 1_R, "-")
 , "/+Product" = binary(0_R, 1_R, "+")
 , "/ ∈ Product" = binary(0_R, 1_R, "∈")
 , "/ /in Product" = binary(0_R, 1_R, "∈")
 , "/ ∉ Product" = binary(0_R, 1_R, "∉")
 , "/ /nin Product" = binary(0_R, 1_R, "∉")
 , "Product Unary Product'" = mergebinary(common, 3, 1_R, 2_R)
 , "* Product' * Unary" = binary(0_R, 1_R, "*")
 , "/ >> Unary" = binary(0_R, 1_R, ">>")
 , "/ << Unary" = binary(0_R, 1_R, "<<")
 , "/ slash Unary" = binary(0_R, 1_R, [slash])
 , "/ mod Unary" = binary(0_R, 1_R, "mod")
 , "/ ∩ Unary" = binary(0_R, 1_R, "∩")
 , "/ ∪ Unary" = binary(0_R, 1_R, "∪")
 , "/ /cap Unary" = binary(0_R, 1_R, "∩")
 , "/ /cup Unary" = binary(0_R, 1_R, "∪")
 , "/ \ Unary" = binary(0_R, 1_R, "\")
 , "Unary-Unary" = unaryMinus(common, 1_R)
 , "/ Id.Unary" = unaryExp(common, 2, 1_R, 2_R)
 , "/ {N} Unary" = unaryExp(common, 3, 1_R, 2_R)
 , "/ Power" = 1_R
 , "Power Atom Power'" = mergebinary(common, 1, 1_R, 2_R)
 , "* Power'_Unary" = binary(0_R, 1_R, "_")
 , "/^Unary" = binary(0_R, 1_R, "^")
 ,
  "Atom (E)"
  = 
   let a = if common then removeparen.1_R else 1_R,
   attribute.prettyR(prec.1_parts.a, width1.a + 2, "(^(text1.a))")
 , "/ [E EL']" = funccall(common, attribute.empty:seq.prettyR, 1_R, 2_R)
 , "/ String" = 1_R
 ,
  "/ Declare Declare' E"
  = combine(common, empty:seq.prettyR, parts.1_R + parts.2_R, 3_R)
 , "/ if E then E IF else E" = fullIfExp(common, R)
 , "/ Name (E EL')" = funccall(common, 1_R, 2_R, 3_R)
 , "/ Name" = 1_R
 ,
  "Name Id:Type"
  = attribute.prettyR(0, width1.1_R + 2 + width1.2_R, text1.1_R + ":" + text1.2_R)
 , "/ Id" = 1_R
 , "Id !, !] !) !:!.! dq any" = 1_R
 , "comma?," = (toAttribute.if common then "" else ",")
 , "/" = toAttribute.""
 ,
  "* IF else if E then E"
  = attribute(parts.0_R + IfExp(common, "/keyword else /keyword if", R))
 ,
  "Type Id.Type"
  = attribute.prettyR(0, width1.1_R + width1.2_R, text1.1_R + "." + text1.2_R)
 , "/ Id" = 1_R
 , "Declare let any = E comma?" = attribute.LetExp(common, 1_R, 2_R, 3_R)
 , "/ assert E report E comma?" = attribute.AssertExp(common, 1_R, 2_R, 3_R)
 ,
  "/ {N} comma?"
  = attribute.CommentExp([prettyR(0, 2, "{")] + parts.1_R + prettyR(0, 2, "}"))
 , "/ for ForDeclare do E comma?" = forExp(1_R, toAttribute."", 2_R, common)
 , "/ for ForDeclare while E do E comma?" = forExp(1_R, 2_R, 3_R, common)
 , "ForDeclare AccumList, any ∈ E" = binary(1_R, AccumExp(common, 2_R, 3_R, "∈"), ",")
 , "/ AccumList, any /in E" = binary(1_R, AccumExp(common, 2_R, 3_R, "∈"), ",")
 , "/ AccumList" = 1_R
 ,
  "AccumList Accum AccumList'"
  = if isempty.text.1_parts.2_R then 1_R else attribute(parts.1_R + parts.2_R)
 , "* AccumList', Accum" = binary(0_R, 1_R, ",")
 , "Accum ! while any = E" = AccumExp(common, 1_R, 2_R, "=")
 , "* Declare' Declare" = attribute(parts.0_R + parts.1_R)
 , "FPL FP FPL'" = attribute(parts.1_R + parts.2_R)
 , "* FPL', FP" = attribute(parts.0_R + prettyR.",^(text1.1_R)")
 ,
  "FP any:Type"
  = attribute.prettyR(0, width1.1_R + 1 + width1.2_R + 1, text1.1_R + ":" + text1.2_R)
 , "/ Type" = 1_R
 ,
  "Header Name (FPL) Type"
  = attribute(prettyR(text1.1_R + "/nosp (") + parts.2_R + prettyR.")^(text1.3_R)")
 , "/ Name Type" = attribute(parts.1_R + parts.2_R)
 , "* Comment C" = attribute(parts.0_R + CommentExp.parts.1_R)
 , "C {N}" = attribute([prettyR(0, 2, "{")] + parts.1_R + prettyR(0, 2, "}"))
 , "* N C" = attribute(parts.0_R + parts.1_R)
 , "/ str1 break" = escape(R, 1)
 , "/ str1 paragraph" = escape(R, 2)
 , "/ str1 row" = escape(R, 3)
 , "/ str1" = attribute(parts.0_R + parts.1_R)
 , "* str1 ! {!} ! row ! paragraph ! break any" = /All
]

<<<< Below is auto generated code >>>>

/br Non-termials:Accum AccumList AccumList' And And' Atom C Comment Compare Compare' Declare Declare'
E EL' FP FPL FPL' ForDeclare Header IF Id N Name Or Or' Power Power' Product Product' S String String'
Sum Sum' Type Unary comma? str1 str2
/br Terminals:() *+,-./and /cap /cup /ge /in /le /ne /nin /or:< << = > >1 >2 >> Builtin Export Function
[\]^_any assert break builtin carrot do dq else for function if is let mod paragraph report row
slash then type unbound while {} ∈ ∉ ∧ ∨ ∩ ∪ ≠ ≤ ≥ ⊻
/br S ← function Header Declare' E / Function Header Declare' E
/br / type Id is FPL Comment
/br / Export type:Type Comment
/br / Export Header Comment
/br / Builtin Header Comment
/br / builtin Header Comment
/br / unbound Header Comment
/br String ← dq String' str2 dq
/br * String' ← str2 carrot (E) / str2 carrot / str2 break
/br / str2 paragraph
/br / str2 row
/br / str2
/br * str2 ← ! dq ! carrot ! row ! paragraph ! break any
/br E ← Or
/br * EL' ←, E
/br Or ← And Or'
/br * Or' ← ∨ And / /or And / ⊻ And
/br And ← Compare And'
/br * And' ← ∧ Compare / /and Compare
/br Compare ← Sum Compare'
/br * Compare' ← = Sum / ≠ Sum / > Sum / < Sum
/br / >1 Sum
/br / >2 Sum
/br / ≥ Sum
/br / /ge Sum
/br / ≤ Sum
/br / /le Sum
/br / /ne Sum
/br Sum ← Product Sum'
/br * Sum' ←-Product /+Product / ∈ Product / /in Product
/br / ∉ Product
/br / /nin Product
/br Product ← Unary Product'
/br * Product' ← * Unary / >> Unary / << Unary / slash Unary
/br / mod Unary
/br / ∩ Unary
/br / ∪ Unary
/br / /cap Unary
/br / /cup Unary
/br / \ Unary
/br Unary ←-Unary / Id.Unary / {N} Unary
/br / Power
/br Power ← Atom Power'
/br * Power' ←_Unary /^Unary
/br Atom ← (E) / [E EL'] / String
/br / Declare Declare' E
/br / if E then E IF else E
/br / Name (E EL')
/br / Name
/br Name ← Id:Type / Id
/br Id ← !, !] !) !:!.! dq any
/br comma? ←, /
/br * IF ← else if E then E
/br Type ← Id.Type / Id
/br Declare ← let any = E comma? / assert E report E comma?
/br / {N} comma?
/br / for ForDeclare do E comma?
/br / for ForDeclare while E do E comma?
/br ForDeclare ← AccumList, any ∈ E / AccumList, any /in E
/br / AccumList
/br AccumList ← Accum AccumList'
/br * AccumList' ←, Accum
/br Accum ← ! while any = E
/br * Declare' ← Declare
/br FPL ← FP FPL'
/br * FPL' ←, FP
/br FP ← any:Type / Type
/br Header ← Name (FPL) Type / Name Type
/br * Comment ← C
/br C ← {N}
/br * N ← C / str1 break / str1 paragraph / str1 row
/br / str1
/br * str1 ← ! {!} ! row ! paragraph ! break any

function action(
 partno:int
 , R:reduction
 , place:int
 , input:seq.word
 , common:boolean
 , parsestk:stack.frame
) attribute
if partno = 2 then
start(common, "function", 1_R, 2_R, 3_R)
else if partno = 3 then
start(common, "Function", 1_R, 2_R, 3_R)
else if partno = 4 then
start("type", 1_R, attribute(parts.2_R + parts.3_R))
else if partno = 5 then
start("Export type:", 1_R, 2_R)
else if partno = 6 then
start("Export", 1_R, 2_R)
else if partno = 7 then
start("Builtin", 1_R, 2_R)
else if partno = 8 then
start("builtin", 1_R, 2_R)
else if partno = 9 then
start("unbound", 1_R, 2_R)
else if partno = 10 then
quote.R
else if partno = 11 then
strEsc.R
else if partno = 12 then
attribute(parts.0_R + prettyR(0, width1.1_R + 2, text1.1_R + "^"))
else if partno = 13 then
escape(R, 1)
else if partno = 14 then
escape(R, 2)
else if partno = 15 then
escape(R, 3)
else if partno = 16 then
attribute(parts.0_R + parts.1_R)
else if partno = 18 then
1_R
else if partno = 19 then
binary(0_R, 1_R, ",")
else if partno = 20 then
mergebinary(common, 8, 1_R, 2_R)
else if partno = 21 then
binary(0_R, 1_R, "∨")
else if partno = 22 then
binary(0_R, 1_R, "∨")
else if partno = 23 then
binary(0_R, 1_R, "⊻")
else if partno = 24 then
mergebinary(common, 7, 1_R, 2_R)
else if partno = 25 then
binary(0_R, 1_R, "∧")
else if partno = 26 then
binary(0_R, 1_R, "∧")
else if partno = 27 then
mergebinary(common, 6, 1_R, 2_R)
else if partno = 28 then
binary(0_R, 1_R, "=")
else if partno = 29 then
binary(0_R, 1_R, "≠")
else if partno = 30 then
binary(0_R, 1_R, ">")
else if partno = 31 then
binary(0_R, 1_R, "<")
else if partno = 32 then
binary(0_R, 1_R, ">1")
else if partno = 33 then
binary(0_R, 1_R, ">2")
else if partno = 34 then
binary(0_R, 1_R, "≥")
else if partno = 35 then
binary(0_R, 1_R, "≥")
else if partno = 36 then
binary(0_R, 1_R, "≤")
else if partno = 37 then
binary(0_R, 1_R, "≤")
else if partno = 38 then
binary(0_R, 1_R, "≠")
else if partno = 39 then
mergebinary(common, 4, 1_R, 2_R)
else if partno = 40 then
binary(0_R, 1_R, "-")
else if partno = 41 then
binary(0_R, 1_R, "+")
else if partno = 42 then
binary(0_R, 1_R, "∈")
else if partno = 43 then
binary(0_R, 1_R, "∈")
else if partno = 44 then
binary(0_R, 1_R, "∉")
else if partno = 45 then
binary(0_R, 1_R, "∉")
else if partno = 46 then
mergebinary(common, 3, 1_R, 2_R)
else if partno = 47 then
binary(0_R, 1_R, "*")
else if partno = 48 then
binary(0_R, 1_R, ">>")
else if partno = 49 then
binary(0_R, 1_R, "<<")
else if partno = 50 then
binary(0_R, 1_R, [slash])
else if partno = 51 then
binary(0_R, 1_R, "mod")
else if partno = 52 then
binary(0_R, 1_R, "∩")
else if partno = 53 then
binary(0_R, 1_R, "∪")
else if partno = 54 then
binary(0_R, 1_R, "∩")
else if partno = 55 then
binary(0_R, 1_R, "∪")
else if partno = 56 then
binary(0_R, 1_R, "\")
else if partno = 57 then
unaryMinus(common, 1_R)
else if partno = 58 then
unaryExp(common, 2, 1_R, 2_R)
else if partno = 59 then
unaryExp(common, 3, 1_R, 2_R)
else if partno = 60 then
1_R
else if partno = 61 then
mergebinary(common, 1, 1_R, 2_R)
else if partno = 62 then
binary(0_R, 1_R, "_")
else if partno = 63 then
binary(0_R, 1_R, "^")
else if partno = 64 then
 let a = if common then removeparen.1_R else 1_R,
 attribute.prettyR(prec.1_parts.a, width1.a + 2, "(^(text1.a))")
else if partno = 65 then
funccall(common, attribute.empty:seq.prettyR, 1_R, 2_R)
else if partno = 66 then
1_R
else if partno = 67 then
combine(common, empty:seq.prettyR, parts.1_R + parts.2_R, 3_R)
else if partno = 68 then
fullIfExp(common, R)
else if partno = 69 then
funccall(common, 1_R, 2_R, 3_R)
else if partno = 70 then
1_R
else if partno = 71 then
attribute.prettyR(0, width1.1_R + 2 + width1.2_R, text1.1_R + ":" + text1.2_R)
else if partno = 72 then
1_R
else if partno = 73 then
1_R
else if partno = 74 then
toAttribute.if common then "" else ","
else if partno = 75 then
toAttribute.""
else if partno = 76 then
attribute(parts.0_R + IfExp(common, "/keyword else /keyword if", R))
else if partno = 77 then
attribute.prettyR(0, width1.1_R + width1.2_R, text1.1_R + "." + text1.2_R)
else if partno = 78 then
1_R
else if partno = 79 then
attribute.LetExp(common, 1_R, 2_R, 3_R)
else if partno = 80 then
attribute.AssertExp(common, 1_R, 2_R, 3_R)
else if partno = 81 then
attribute.CommentExp([prettyR(0, 2, "{")] + parts.1_R + prettyR(0, 2, "}"))
else if partno = 82 then
forExp(1_R, toAttribute."", 2_R, common)
else if partno = 83 then
forExp(1_R, 2_R, 3_R, common)
else if partno = 84 then
binary(1_R, AccumExp(common, 2_R, 3_R, "∈"), ",")
else if partno = 85 then
binary(1_R, AccumExp(common, 2_R, 3_R, "∈"), ",")
else if partno = 86 then
1_R
else if partno = 87 then
if isempty.text.1_parts.2_R then 1_R else attribute(parts.1_R + parts.2_R)
else if partno = 88 then
binary(0_R, 1_R, ",")
else if partno = 89 then
AccumExp(common, 1_R, 2_R, "=")
else if partno = 90 then
attribute(parts.0_R + parts.1_R)
else if partno = 91 then
attribute(parts.1_R + parts.2_R)
else if partno = 92 then
attribute(parts.0_R + prettyR.",^(text1.1_R)")
else if partno = 93 then
attribute.prettyR(0, width1.1_R + 1 + width1.2_R + 1, text1.1_R + ":" + text1.2_R)
else if partno = 94 then
1_R
else if partno = 95 then
attribute(prettyR(text1.1_R + "/nosp (") + parts.2_R + prettyR.")^(text1.3_R)")
else if partno = 96 then
attribute(parts.1_R + parts.2_R)
else if partno = 97 then
attribute(parts.0_R + CommentExp.parts.1_R)
else if partno = 98 then
attribute([prettyR(0, 2, "{")] + parts.1_R + prettyR(0, 2, "}"))
else if partno = 99 then
attribute(parts.0_R + parts.1_R)
else if partno = 100 then
escape(R, 1)
else if partno = 101 then
escape(R, 2)
else if partno = 102 then
escape(R, 3)
else if partno = 103 then
attribute(parts.0_R + parts.1_R)
else 0_R

function mytable seq.tblEle
[
 tblEle(S.2, 1_"S", Reduce.1, Fail)
 , tblEle(Match, 1_"function", S.3, S.6)
 , tblEle(S.294, 1_"Header", S.4, S.6)
 , tblEle(S.283, 1_"Declare'", S.5, S.6)
 , tblEle(S.62, 1_"E", Reduce.2, S.6)
 , tblEle(Match, 1_"Function", S.7, S.10)
 , tblEle(S.294, 1_"Header", S.8, S.10)
 , tblEle(S.283, 1_"Declare'", S.9, S.10)
 , tblEle(S.62, 1_"E", Reduce.3, S.10)
 , tblEle(Match, 1_"type", S.11, S.15)
 , tblEle(S.218, 1_"Id", S.12, S.15)
 , tblEle(Match, 1_"is", S.13, S.15)
 , tblEle(S.285, 1_"FPL", S.14, S.15)
 , tblEle(S.301, 1_"Comment", Reduce.4, S.15)
 , tblEle(Match, 1_"Export", S.16, S.20)
 , tblEle(MatchNext, 1_"type", S.17, S.21)
 , tblEle(Match, 1_":", S.18, S.20)
 , tblEle(S.233, 1_"Type", S.19, S.20)
 , tblEle(S.301, 1_"Comment", Reduce.5, S.20)
 , tblEle(Match, 1_"Export", S.21, S.23)
 , tblEle(S.294, 1_"Header", S.22, S.23)
 , tblEle(S.301, 1_"Comment", Reduce.6, S.23)
 , tblEle(Match, 1_"Builtin", S.24, S.26)
 , tblEle(S.294, 1_"Header", S.25, S.26)
 , tblEle(S.301, 1_"Comment", Reduce.7, S.26)
 , tblEle(Match, 1_"builtin", S.27, S.29)
 , tblEle(S.294, 1_"Header", S.28, S.29)
 , tblEle(S.301, 1_"Comment", Reduce.8, S.29)
 , tblEle(Match, 1_"unbound", S.30, Fail)
 , tblEle(S.294, 1_"Header", S.31, Fail)
 , tblEle(S.301, 1_"Comment", Reduce.9, Fail)
 , tblEle(Match, 1_dq, S.33, Fail)
 , tblEle(S.36, 1_"String'", S.34, Fail)
 , tblEle(S.56, 1_"str2", S.35, Fail)
 , tblEle(Match, 1_dq, Reduce.10, Fail)
 , tblEle(S.56, 1_"str2", S.37, S.42)
 , tblEle(MatchNext, 1_"^", S.38, S.43)
 , tblEle(MatchNext, 1_"(", S.39, S.44)
 , tblEle(S.62, 1_"E", S.40, S.42)
 , tblEle(Match, 1_")", S.41, S.42)
 , tblEle(Reduce.11, 1_"?", S.36, S.0)
 , tblEle(S.56, 1_"str2", S.43, S.45)
 , tblEle(MatchNext, 1_"^", S.44, S.46)
 , tblEle(Reduce.12, 1_"?", S.36, S.0)
 , tblEle(S.56, 1_"str2", S.46, S.48)
 , tblEle(MatchNext, break, S.47, S.49)
 , tblEle(Reduce.13, 1_"?", S.36, S.0)
 , tblEle(S.56, 1_"str2", S.49, S.51)
 , tblEle(MatchNext, paragraph, S.50, S.52)
 , tblEle(Reduce.14, 1_"?", S.36, S.0)
 , tblEle(S.56, 1_"str2", S.52, S.54)
 , tblEle(MatchNext, row, S.53, S.55)
 , tblEle(Reduce.15, 1_"?", S.36, S.0)
 , tblEle(S.56, 1_"str2", S.55, Success*)
 , tblEle(Reduce.16, 1_"?", S.36, S.0)
 , tblEle(!Match, 1_dq, S.57, All)
 , tblEle(!Match, 1_"^", S.58, All)
 , tblEle(!Match, row, S.59, All)
 , tblEle(!Match, paragraph, S.60, All)
 , tblEle(!Match, break, S.61, All)
 , tblEle(MatchAny, 1_"any", Discard*.56, All)
 , tblEle(S.66, 1_"Or", Reduce.18, Fail)
 , tblEle(Match, 1_",", S.64, Success*)
 , tblEle(S.62, 1_"E", S.65, Success*)
 , tblEle(Reduce.19, 1_"?", S.63, S.0)
 , tblEle(S.77, 1_"And", S.67, Fail)
 , tblEle(S.68, 1_"Or'", Reduce.20, Fail)
 , tblEle(Match, 1_"∨", S.69, S.71)
 , tblEle(S.77, 1_"And", S.70, S.71)
 , tblEle(Reduce.21, 1_"?", S.68, S.0)
 , tblEle(Match, 1_"/or", S.72, S.74)
 , tblEle(S.77, 1_"And", S.73, S.74)
 , tblEle(Reduce.22, 1_"?", S.68, S.0)
 , tblEle(Match, 1_"⊻", S.75, Success*)
 , tblEle(S.77, 1_"And", S.76, Success*)
 , tblEle(Reduce.23, 1_"?", S.68, S.0)
 , tblEle(S.85, 1_"Compare", S.78, Fail)
 , tblEle(S.79, 1_"And'", Reduce.24, Fail)
 , tblEle(Match, 1_"∧", S.80, S.82)
 , tblEle(S.85, 1_"Compare", S.81, S.82)
 , tblEle(Reduce.25, 1_"?", S.79, S.0)
 , tblEle(Match, 1_"/and", S.83, Success*)
 , tblEle(S.85, 1_"Compare", S.84, Success*)
 , tblEle(Reduce.26, 1_"?", S.79, S.0)
 , tblEle(S.120, 1_"Sum", S.86, Fail)
 , tblEle(S.87, 1_"Compare'", Reduce.27, Fail)
 , tblEle(Match, 1_"=", S.88, S.90)
 , tblEle(S.120, 1_"Sum", S.89, S.90)
 , tblEle(Reduce.28, 1_"?", S.87, S.0)
 , tblEle(Match, 1_"≠", S.91, S.93)
 , tblEle(S.120, 1_"Sum", S.92, S.93)
 , tblEle(Reduce.29, 1_"?", S.87, S.0)
 , tblEle(Match, 1_">", S.94, S.96)
 , tblEle(S.120, 1_"Sum", S.95, S.96)
 , tblEle(Reduce.30, 1_"?", S.87, S.0)
 , tblEle(Match, 1_"<", S.97, S.99)
 , tblEle(S.120, 1_"Sum", S.98, S.99)
 , tblEle(Reduce.31, 1_"?", S.87, S.0)
 , tblEle(Match, 1_">1", S.100, S.102)
 , tblEle(S.120, 1_"Sum", S.101, S.102)
 , tblEle(Reduce.32, 1_"?", S.87, S.0)
 , tblEle(Match, 1_">2", S.103, S.105)
 , tblEle(S.120, 1_"Sum", S.104, S.105)
 , tblEle(Reduce.33, 1_"?", S.87, S.0)
 , tblEle(Match, 1_"≥", S.106, S.108)
 , tblEle(S.120, 1_"Sum", S.107, S.108)
 , tblEle(Reduce.34, 1_"?", S.87, S.0)
 , tblEle(Match, 1_"/ge", S.109, S.111)
 , tblEle(S.120, 1_"Sum", S.110, S.111)
 , tblEle(Reduce.35, 1_"?", S.87, S.0)
 , tblEle(Match, 1_"≤", S.112, S.114)
 , tblEle(S.120, 1_"Sum", S.113, S.114)
 , tblEle(Reduce.36, 1_"?", S.87, S.0)
 , tblEle(Match, 1_"/le", S.115, S.117)
 , tblEle(S.120, 1_"Sum", S.116, S.117)
 , tblEle(Reduce.37, 1_"?", S.87, S.0)
 , tblEle(Match, 1_"/ne", S.118, Success*)
 , tblEle(S.120, 1_"Sum", S.119, Success*)
 , tblEle(Reduce.38, 1_"?", S.87, S.0)
 , tblEle(S.140, 1_"Product", S.121, Fail)
 , tblEle(S.122, 1_"Sum'", Reduce.39, Fail)
 , tblEle(Match, 1_"-", S.123, S.125)
 , tblEle(S.140, 1_"Product", S.124, S.125)
 , tblEle(Reduce.40, 1_"?", S.122, S.0)
 , tblEle(Match, 1_"+", S.126, S.128)
 , tblEle(S.140, 1_"Product", S.127, S.128)
 , tblEle(Reduce.41, 1_"?", S.122, S.0)
 , tblEle(Match, 1_"∈", S.129, S.131)
 , tblEle(S.140, 1_"Product", S.130, S.131)
 , tblEle(Reduce.42, 1_"?", S.122, S.0)
 , tblEle(Match, 1_"/in", S.132, S.134)
 , tblEle(S.140, 1_"Product", S.133, S.134)
 , tblEle(Reduce.43, 1_"?", S.122, S.0)
 , tblEle(Match, 1_"∉", S.135, S.137)
 , tblEle(S.140, 1_"Product", S.136, S.137)
 , tblEle(Reduce.44, 1_"?", S.122, S.0)
 , tblEle(Match, 1_"/nin", S.138, Success*)
 , tblEle(S.140, 1_"Product", S.139, Success*)
 , tblEle(Reduce.45, 1_"?", S.122, S.0)
 , tblEle(S.172, 1_"Unary", S.141, Fail)
 , tblEle(S.142, 1_"Product'", Reduce.46, Fail)
 , tblEle(Match, 1_"*", S.143, S.145)
 , tblEle(S.172, 1_"Unary", S.144, S.145)
 , tblEle(Reduce.47, 1_"?", S.142, S.0)
 , tblEle(Match, 1_">>", S.146, S.148)
 , tblEle(S.172, 1_"Unary", S.147, S.148)
 , tblEle(Reduce.48, 1_"?", S.142, S.0)
 , tblEle(Match, 1_"<<", S.149, S.151)
 , tblEle(S.172, 1_"Unary", S.150, S.151)
 , tblEle(Reduce.49, 1_"?", S.142, S.0)
 , tblEle(Match, slash, S.152, S.154)
 , tblEle(S.172, 1_"Unary", S.153, S.154)
 , tblEle(Reduce.50, 1_"?", S.142, S.0)
 , tblEle(Match, 1_"mod", S.155, S.157)
 , tblEle(S.172, 1_"Unary", S.156, S.157)
 , tblEle(Reduce.51, 1_"?", S.142, S.0)
 , tblEle(Match, 1_"∩", S.158, S.160)
 , tblEle(S.172, 1_"Unary", S.159, S.160)
 , tblEle(Reduce.52, 1_"?", S.142, S.0)
 , tblEle(Match, 1_"∪", S.161, S.163)
 , tblEle(S.172, 1_"Unary", S.162, S.163)
 , tblEle(Reduce.53, 1_"?", S.142, S.0)
 , tblEle(Match, 1_"/cap", S.164, S.166)
 , tblEle(S.172, 1_"Unary", S.165, S.166)
 , tblEle(Reduce.54, 1_"?", S.142, S.0)
 , tblEle(Match, 1_"/cup", S.167, S.169)
 , tblEle(S.172, 1_"Unary", S.168, S.169)
 , tblEle(Reduce.55, 1_"?", S.142, S.0)
 , tblEle(Match, 1_"\", S.170, Success*)
 , tblEle(S.172, 1_"Unary", S.171, Success*)
 , tblEle(Reduce.56, 1_"?", S.142, S.0)
 , tblEle(Match, 1_"-", S.173, S.174)
 , tblEle(S.172, 1_"Unary", Reduce.57, S.174)
 , tblEle(S.218, 1_"Id", S.175, S.177)
 , tblEle(Match, 1_".", S.176, S.177)
 , tblEle(S.172, 1_"Unary", Reduce.58, S.177)
 , tblEle(Match, 1_"{", S.178, S.181)
 , tblEle(S.306, 1_"N", S.179, S.181)
 , tblEle(Match, 1_"}", S.180, S.181)
 , tblEle(S.172, 1_"Unary", Reduce.59, S.181)
 , tblEle(S.182, 1_"Power", Reduce.60, Fail)
 , tblEle(S.190, 1_"Atom", S.183, Fail)
 , tblEle(S.184, 1_"Power'", Reduce.61, Fail)
 , tblEle(Match, 1_"_", S.185, S.187)
 , tblEle(S.172, 1_"Unary", S.186, S.187)
 , tblEle(Reduce.62, 1_"?", S.184, S.0)
 , tblEle(Match, 1_"^", S.188, Success*)
 , tblEle(S.172, 1_"Unary", S.189, Success*)
 , tblEle(Reduce.63, 1_"?", S.184, S.0)
 , tblEle(Match, 1_"(", S.191, S.193)
 , tblEle(S.62, 1_"E", S.192, S.193)
 , tblEle(Match, 1_")", Reduce.64, S.193)
 , tblEle(Match, 1_"[", S.194, S.197)
 , tblEle(S.62, 1_"E", S.195, S.197)
 , tblEle(S.63, 1_"EL'", S.196, S.197)
 , tblEle(Match, 1_"]", Reduce.65, S.197)
 , tblEle(S.32, 1_"String", Reduce.66, S.198)
 , tblEle(S.237, 1_"Declare", S.199, S.201)
 , tblEle(S.283, 1_"Declare'", S.200, S.201)
 , tblEle(S.62, 1_"E", Reduce.67, S.201)
 , tblEle(Match, 1_"if", S.202, S.208)
 , tblEle(S.62, 1_"E", S.203, S.208)
 , tblEle(Match, 1_"then", S.204, S.208)
 , tblEle(S.62, 1_"E", S.205, S.208)
 , tblEle(S.227, 1_"IF", S.206, S.208)
 , tblEle(Match, 1_"else", S.207, S.208)
 , tblEle(S.62, 1_"E", Reduce.68, S.208)
 , tblEle(S.214, 1_"Name", S.209, S.213)
 , tblEle(MatchNext, 1_"(", S.210, Reduce.70)
 , tblEle(S.62, 1_"E", S.211, S.213)
 , tblEle(S.63, 1_"EL'", S.212, S.213)
 , tblEle(Match, 1_")", Reduce.69, S.213)
 , tblEle(S.214, 1_"Name", Reduce.70, Fail)
 , tblEle(S.218, 1_"Id", S.215, S.217)
 , tblEle(MatchNext, 1_":", S.216, Reduce.72)
 , tblEle(S.233, 1_"Type", Reduce.71, S.217)
 , tblEle(S.218, 1_"Id", Reduce.72, Fail)
 , tblEle(!Match, 1_",", S.219, Fail)
 , tblEle(!Match, 1_"]", S.220, Fail)
 , tblEle(!Match, 1_")", S.221, Fail)
 , tblEle(!Match, 1_":", S.222, Fail)
 , tblEle(!Match, 1_".", S.223, Fail)
 , tblEle(!Match, 1_dq, S.224, Fail)
 , tblEle(MatchAny, 1_"any", Reduce.73, Fail)
 , tblEle(Match, 1_",", Reduce.74, S.226)
 , tblEle(Reduce.75, 1_"?", S.0, S.0)
 , tblEle(Match, 1_"else", S.228, Success*)
 , tblEle(Match, 1_"if", S.229, Success*)
 , tblEle(S.62, 1_"E", S.230, Success*)
 , tblEle(Match, 1_"then", S.231, Success*)
 , tblEle(S.62, 1_"E", S.232, Success*)
 , tblEle(Reduce.76, 1_"?", S.227, S.0)
 , tblEle(S.218, 1_"Id", S.234, S.236)
 , tblEle(MatchNext, 1_".", S.235, Reduce.78)
 , tblEle(S.233, 1_"Type", Reduce.77, S.236)
 , tblEle(S.218, 1_"Id", Reduce.78, Fail)
 , tblEle(Match, 1_"let", S.238, S.242)
 , tblEle(MatchAny, 1_"any", S.239, S.242)
 , tblEle(Match, 1_"=", S.240, S.242)
 , tblEle(S.62, 1_"E", S.241, S.242)
 , tblEle(S.225, 1_"comma?", Reduce.79, S.242)
 , tblEle(Match, 1_"assert", S.243, S.247)
 , tblEle(S.62, 1_"E", S.244, S.247)
 , tblEle(Match, 1_"report", S.245, S.247)
 , tblEle(S.62, 1_"E", S.246, S.247)
 , tblEle(S.225, 1_"comma?", Reduce.80, S.247)
 , tblEle(Match, 1_"{", S.248, S.251)
 , tblEle(S.306, 1_"N", S.249, S.251)
 , tblEle(Match, 1_"}", S.250, S.251)
 , tblEle(S.225, 1_"comma?", Reduce.81, S.251)
 , tblEle(Match, 1_"for", S.252, S.256)
 , tblEle(S.263, 1_"ForDeclare", S.253, P.257)
 , tblEle(MatchNext, 1_"do", S.254, S.258)
 , tblEle(S.62, 1_"E", S.255, S.256)
 , tblEle(S.225, 1_"comma?", Reduce.82, S.256)
 , tblEle(Match, 1_"for", S.257, Fail)
 , tblEle(S.263, 1_"ForDeclare", S.258, Fail)
 , tblEle(Match, 1_"while", S.259, Fail)
 , tblEle(S.62, 1_"E", S.260, Fail)
 , tblEle(Match, 1_"do", S.261, Fail)
 , tblEle(S.62, 1_"E", S.262, Fail)
 , tblEle(S.225, 1_"comma?", Reduce.83, Fail)
 , tblEle(S.274, 1_"AccumList", S.264, S.268)
 , tblEle(MatchNext, 1_",", S.265, S.269)
 , tblEle(MatchAny, 1_"any", S.266, S.268)
 , tblEle(MatchNext, 1_"∈", S.267, S.271)
 , tblEle(S.62, 1_"E", Reduce.84, S.268)
 , tblEle(S.274, 1_"AccumList", S.269, S.273)
 , tblEle(MatchNext, 1_",", S.270, Reduce.86)
 , tblEle(MatchAny, 1_"any", S.271, S.273)
 , tblEle(Match, 1_"/in", S.272, S.273)
 , tblEle(S.62, 1_"E", Reduce.85, S.273)
 , tblEle(S.274, 1_"AccumList", Reduce.86, Fail)
 , tblEle(S.279, 1_"Accum", S.275, Fail)
 , tblEle(S.276, 1_"AccumList'", Reduce.87, Fail)
 , tblEle(Match, 1_",", S.277, Success*)
 , tblEle(S.279, 1_"Accum", S.278, Success*)
 , tblEle(Reduce.88, 1_"?", S.276, S.0)
 , tblEle(!Match, 1_"while", S.280, Fail)
 , tblEle(MatchAny, 1_"any", S.281, Fail)
 , tblEle(Match, 1_"=", S.282, Fail)
 , tblEle(S.62, 1_"E", Reduce.89, Fail)
 , tblEle(S.237, 1_"Declare", S.284, Success*)
 , tblEle(Reduce.90, 1_"?", S.283, S.0)
 , tblEle(S.290, 1_"FP", S.286, Fail)
 , tblEle(S.287, 1_"FPL'", Reduce.91, Fail)
 , tblEle(Match, 1_",", S.288, Success*)
 , tblEle(S.290, 1_"FP", S.289, Success*)
 , tblEle(Reduce.92, 1_"?", S.287, S.0)
 , tblEle(MatchAny, 1_"any", S.291, S.293)
 , tblEle(Match, 1_":", S.292, S.293)
 , tblEle(S.233, 1_"Type", Reduce.93, S.293)
 , tblEle(S.233, 1_"Type", Reduce.94, Fail)
 , tblEle(S.214, 1_"Name", S.295, S.299)
 , tblEle(MatchNext, 1_"(", S.296, S.300)
 , tblEle(S.285, 1_"FPL", S.297, S.299)
 , tblEle(Match, 1_")", S.298, S.299)
 , tblEle(S.233, 1_"Type", Reduce.95, S.299)
 , tblEle(S.214, 1_"Name", S.300, Fail)
 , tblEle(S.233, 1_"Type", Reduce.96, Fail)
 , tblEle(S.303, 1_"C", S.302, Success*)
 , tblEle(Reduce.97, 1_"?", S.301, S.0)
 , tblEle(Match, 1_"{", S.304, Fail)
 , tblEle(S.306, 1_"N", S.305, Fail)
 , tblEle(Match, 1_"}", Reduce.98, Fail)
 , tblEle(S.303, 1_"C", S.307, S.308)
 , tblEle(Reduce.99, 1_"?", S.306, S.0)
 , tblEle(S.319, 1_"str1", S.309, S.311)
 , tblEle(MatchNext, break, S.310, S.312)
 , tblEle(Reduce.100, 1_"?", S.306, S.0)
 , tblEle(S.319, 1_"str1", S.312, S.314)
 , tblEle(MatchNext, paragraph, S.313, S.315)
 , tblEle(Reduce.101, 1_"?", S.306, S.0)
 , tblEle(S.319, 1_"str1", S.315, S.317)
 , tblEle(MatchNext, row, S.316, S.318)
 , tblEle(Reduce.102, 1_"?", S.306, S.0)
 , tblEle(S.319, 1_"str1", S.318, Success*)
 , tblEle(Reduce.103, 1_"?", S.306, S.0)
 , tblEle(!Match, 1_"{", S.320, All)
 , tblEle(!Match, 1_"}", S.321, All)
 , tblEle(!Match, row, S.322, All)
 , tblEle(!Match, paragraph, S.323, All)
 , tblEle(!Match, break, S.324, All)
 , tblEle(MatchAny, 1_"any", Discard*.319, All)
]

function =(seq.word, attribute) boolean true

function =(seq.word, word) boolean true

use standard

use seq.tblEle

use otherseq.frame

use stack.frame

use otherseq.attribute

use PEGrules

function _(i:int, R:reduction) attribute (i + 1)_toseq.R

type tblEle is action:state, match:word, Sstate:state, Fstate:state

type reduction is toseq:seq.attribute

type frame is
Sstate:state
, Fstate:state
, i:int
, result:seq.attribute
, faili:int
, failresult:seq.attribute

type runresult is stk:stack.frame

Function success(a:runresult) boolean Sstate.top.stk.a ≠ Fail

Function result(a:runresult) attribute 1^result.top.stk.a

function parse(
 myinput:seq.word
 , table:seq.tblEle
 , initAttr:attribute
 , common:boolean
) runresult
let packedTable = packed.table
for
 stk = empty:stack.frame
 , state = startstate
 , i = 1
 , result = [initAttr]
 , faili = 1
 , failresult = [initAttr]
while not(
 index.state = 1 ∧ action.state = actionReduce
 ∨ action.state = Fail ∧ n.toseq.stk < 2
)
do
 let actionState = action.state,
  if actionState = Fail ∨ actionState = actionReduce ∧ not.isempty.stk ∧ is!.Sstate.top.stk then
   {goto Fstate.top.stk, i = faili.top, pop.stk, discard result}
   let top = top.stk
   let newstk = pop.stk,
    if action.Fstate.top = actionP then
    next(newstk, S.index.Fstate.top, i.top, result.top, faili.top, failresult.top)
    else next(
     newstk
     , if is!.Sstate.top ∧ state = Fail then Sstate.top else Fstate.top
     , faili.top
     , failresult.top
     , faili.top
     , failresult.top
    )
  else if actionState = Success* then
   {goto Sstate.top.stk, pop.stk, keep result}
   let top = top.stk, next(pop.stk, Sstate.top, i, result.top + result, faili.top, failresult.top)
  else if actionState = actionDiscard* then
  next(stk, S.index.state, i, result, i, result)
  else if actionState = All then
   let top = top.stk
   let reduction = [toAttribute(1^result, subseq(myinput, i.top, i - 1))],
   next(pop.stk, Sstate.top, i, result.top + reduction, faili.top, failresult.top)
  else if actionState = actionReduce then
   {actionReduce}
   let top = top.stk
   let reduction = [action(index.state, reduction.result, i, myinput, common, stk)],
   next(pop.stk, Sstate.top, i, result.top + reduction, faili.top, failresult.top)
  else
   let iz = index.state
   let te = idxNB(packedTable, iz)
   let actionTe = action.action.te,
    if actionTe = S.0 then
     {match non Terminal}
     let newstk = push(stk, frame(Sstate.te, Fstate.te, i, result, faili, failresult))
     let tmp = [toAttribute(1^result, empty:seq.word)],
     next(newstk, action.te, i, tmp, i, tmp)
    else if actionTe = actionReduce then
     let reduction = [action(index.action.te, reduction.result, i, myinput, common, stk)]
     let top = top.stk,
      if faili = i then
      next(pop.stk, Sstate.top, i, result.top + reduction, faili.top, failresult.top)
      else next(stk, Sstate.te, i, reduction, i, reduction)
    else if actionTe = Match then
     if i > n.myinput ∨ i_myinput ≠ match.te then
     {fail} next(stk, Fstate.te, faili, failresult, faili, failresult)
     else next(stk, Sstate.te, i + 1, result, faili, failresult)
    else if actionTe = MatchNext then
     if i > n.myinput ∨ i_myinput ≠ match.te then
     {fail} next(stk, Fstate.te, i, result, faili, failresult)
     else next(stk, Sstate.te, i + 1, result, faili, failresult)
    else if actionTe = !Match then
     if i ≤ n.myinput ∧ i_myinput = match.te then
     {fail} next(stk, Fstate.te, faili, failresult, faili, failresult)
     else next(stk, Sstate.te, i, result, faili, failresult)
    else
     assert actionTe = MatchAny report "PROBLEM PEG",
      if i > n.myinput then
      {fail} next(stk, Fstate.te, i, result, faili, failresult)
      else
       let newresult =
        if action.Sstate.te = actionDiscard* then
        result
        else result + toAttribute(1^result, [i_myinput])
       ,
       next(stk, Sstate.te, i + 1, newresult, faili, failresult)
,
runresult.push(stk, frame(state, state, i, result, i, result)) 