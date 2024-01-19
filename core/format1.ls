Module format1

use PEGrules

use UTF8

use bits

use otherseq.byte

use otherseq.int

use set.int

use standard

use seq.tableEntry

use seq.word

use otherseq.seq.word

function showZ(out:seq.word) seq.word
for acc = "", w ∈ out do acc + encodeword(decodeword.w + char1."Z"),
acc

function toAttribute(a:seq.byte, b:seq.word) seq.byte X.b

function escape&<(a:seq.byte) seq.byte
let lt = tobyte.toint.char1."<"
let amp = tobyte.toint.char1."&"
for i = 1, e ∈ a while e ≠ lt ∧ e ≠ amp do i + 1,
if i > n.a then a
else
 subseq(a, 1, i - 1)
  + (if i#a = amp then X."&amp;" else X."&lt;")
  + escape&<(a << i)

function X(a:seq.word) seq.byte
for acc0 = empty:seq.byte, w ∈ a
do
 for acc = acc0, ch ∈ decodeword.w
 do acc + if toint.ch < 128 then [tobyte.toint.ch] else toseqbyte.encodeUTF8.ch,
 acc + tobyte.32,
acc0 >> 1

Function textFormat1(myinput:seq.word) UTF8
{OPTION NOINLINE}
let r = parse(myinput, empty:seq.byte, true)
{assert false report trace.r}
UTF8(result.r + tobyte.32)

Function HTMLformat1(myinput:seq.word) UTF8
{OPTION NOINLINE}
let r = parse(myinput, empty:seq.byte, false)
{assert false report}
UTF8(result.r + tobyte.32)

function span(class:seq.byte, b:seq.byte) seq.byte
X."<span"
 + tobyte.32
 + X."class"
 + X."="
 + class
 + X.">"
 + b
 + tobyte.32
 + X."</span>"

function addSpace(a:seq.byte) seq.byte
if isempty.a ∨ 1^a = tobyte.32 then a else a + tobyte.32

function block(R0:seq.byte, R1:seq.byte, text:boolean) seq.byte
if isempty.R1 then R0
else if text then
 let body = if 1^R1 = tobyte.10 then R1 >> 1 else R1
 let init =
  linebreak.R0
   + if subseq(body, 1, 1) = [tobyte.32] then empty:seq.byte else [tobyte.32],
 for acc = init, b ∈ body
 do if b = tobyte.10 then acc + b + tobyte.32 else acc + b,
 linebreak.acc
else R0 + span(X."block", R1)

function paragraph(a:seq.byte) seq.byte
{used for text and not html}
a + if isempty.a ∨ 1^a ≠ tobyte.10 then [tobyte.10] + tobyte.10 else [tobyte.10]

function linebreak(a:seq.byte) seq.byte
{used for text and not html}
if isempty.a ∨ 1^a ≠ tobyte.10 then a + [tobyte.10] else a

CN process commands with no space pending

CS process commands with space pending

N no commands with no space pending

S no commands with space pending

NSBA no space before or after

NSB no space before

function endMark word encodeword.[char.254]

use PEGrules

use seq.tableEntry

use stack.frame

use seq.seq.byte

function break word 1#"/br"

function /<* word 1#"<* m *>"

function /*> word 1^"<* m *>"

function PEGgen(
seqElementType:word
, attributeType:seq.byte
, resultType:thisresult
, textOut:boolean
, commonType:boolean
) seq.boolean
{commonName: textOut notablex: wordmap: dq 1#dq, ec escapeformat, tag merge." / ta g", break 1#"
/br", /<* /<*, /*> /*>, 1#" $"}
[
 "* CN+" = $.0 + X."+"
 , "/-" = $.0 + X."-"
 , "/." = $.0 + X."."
 , "/:" = $.0 + X.":"
 , "/. " = $.0 + X.". "
 , "/: " = $.0 + X.": "
 , "/#" = $.0 + X."#"
 , "/^" = $.0 + X."^"
 , "/ /sp" = addSpace.$.0
 , "/ tag ! ec any" = $.0 + $.1
 , "/ break" = (if textOut then linebreak.$.0 else $.0 + X."<br>")
 , "/ /<* block CN /*>" = block($.0, $.1, textOut)
 , "/ /<* table CN /*>"
 = (if textOut then $.0 + $.1 else $.0 + X."<table>" + $.1 + X."</table>")
 , "/
 /p"
 = (if textOut then paragraph.$.0 else $.0 + X."<p>")
 , "/ ec N" = $.0 + $.1
 , "/ CS+" = $.0 + $.1 + X."+"
 , "/ CS-" = $.0 + $.1 + X."-"
 , "/ CS." = $.0 + $.1 + X."."
 , "/ CS:" = $.0 + $.1 + X.":"
 , "/ CS. " = $.0 + $.1 + X.". "
 , "/ CS: " = $.0 + $.1 + X.": "
 , "/ CS#" = $.0 + $.1 + X."#"
 , "/ CS^" = $.0 + $.1 + X."^"
 , "/ CS (" = $.0 + addSpace.$.1 + X."("
 , "/ CS {" = $.0 + addSpace.$.1 + X."{"
 , "/ CS [" = $.0 + addSpace.$.1 + X."["
 , "/ CS" = $.0 + $.1
 , "/+" = $.0 + X."+"
 , "/-" = $.0 + X."-"
 , "/." = $.0 + X."."
 , "/:" = $.0 + X.":"
 , "/. " = $.0 + X.". "
 , "/: " = $.0 + X.": "
 , "/#" = $.0 + X."#"
 , "/^" = $.0 + X."^"
 , "/ (" = $.0 + X."("
 , "/ {" = $.0 + X."{"
 , "/ [" = $.0 + X."["
 , "+CS)" = $.0 + X.")"
 , "/ dq" = $.0 + X.dq
 , "/," = $.0 + X.","
 , "/]" = $.0 + X."]"
 , "/}" = $.0 + X."}"
 , "/ /keyword any"
 = addSpace.$.0 + (if textOut then $.1 else span(X."keyword", escape&<.$.1))
 , "/ /em any !. "
 = addSpace.$.0
  + (if textOut then $.1 else X."<em>" + addSpace.escape&<.$.1 + X."</em>")
 , "/ /em any"
 = addSpace.$.0 + (if textOut then $.1 else X."<em>" + escape&<.$.1 + X."</em>")
 , "/ /strong any !. "
 = addSpace.$.0
  + (if textOut then $.1 else X."<strong>" + addSpace.escape&<.$.1 + X."</strong>")
 , "/ /strong any"
 = addSpace.$.0 + (if textOut then $.1 else X."<strong>" + escape&<.$.1 + X."</strong>")
 , "/ /cell" = (if textOut then $.0 else $.0 + X."<td>")
 , "/
 /row"
 = (if textOut then $.0 + tobyte.10 else $.0 + X."<tr><td>")
 , "/ /<* ! block ! table any CN /*>"
 = addSpace.$.0 + (if textOut then $.2 else span($.1, $.2))
 , "/ /sp" = addSpace.$.0
 , "/ !+!-!.!:!. !: !#!^! (! [! {! !
 /p ! /strong ! /em ! break ! /<* ! /*> ! ec ! tag any"
 = addSpace.$.0 + (if textOut then $.1 else escape&<.$.1)
 , "N N' ec CN" = $.1 + $.2
 , "* N' S+" = $.0 + $.1 + X."+"
 , "/ S-" = $.0 + $.1 + X."-"
 , "/ S." = $.0 + $.1 + X."."
 , "/ S:" = $.0 + $.1 + X.":"
 , "/ S. " = $.0 + $.1 + X.". "
 , "/ S: " = $.0 + $.1 + X.": "
 , "/ S#" = $.0 + $.1 + X."#"
 , "/ S^" = $.0 + $.1 + X."^"
 , "/ S (" = $.0 + addSpace.$.1 + X."("
 , "/ S {" = $.0 + addSpace.$.1 + X."{"
 , "/ S [" = $.0 + addSpace.$.1 + X."["
 , "/ S" = $.0 + $.1
 , "/+" = $.0 + X."+"
 , "/-" = $.0 + X."-"
 , "/." = $.0 + X."."
 , "/:" = $.0 + X.":"
 , "/. " = $.0 + X.". "
 , "/: " = $.0 + X.": "
 , "/#" = $.0 + X."#"
 , "/^" = $.0 + X."^"
 , "/ (" = $.0 + X."("
 , "/ {" = $.0 + X."{"
 , "/ [" = $.0 + X."["
 , "+S)" = $.0 + X.")"
 , "/ dq" = $.0 + X.dq
 , "/," = $.0 + X.","
 , "/]" = $.0 + X."]"
 , "/}" = $.0 + X."}"
 , "/ !+!-!.!:!. !: !#!^! (! [! {! ec any"
 = addSpace.$.0 + (if textOut then $.1 else escape&<.$.1)
 , "NSA. " = X.""
 , "/:" = X.""
]

<<<< Below is auto generated code >>>>

/br Unused non-terminals:NSA
/br Non-terminals:CN CS N N' NSA S
/br Terminals:#()+,-.. /*> /<* /cell /em /keyword
/p
/row /sp /strong:: []^any block break dq ec table tag {}
/br * CN ←+/-/./:/. /: /#/^/ /sp / tag ! ec any / break / /<* block CN /*> / /<* table CN /*> /
/p / ec N / CS+/ CS-/ CS./ CS:/ CS. / CS: / CS#/ CS^/ CS (/ CS {/ CS [/ CS /+/-/./:/. /: /#/^/ (/ {/ [
/br+CS ←) / dq /, /] /} / /keyword any / /em any !. / /em any / /strong any !. / /strong any / /cell /
/row / /<* ! block ! table any CN /*> / /sp / !+!-!.!:!. !: !#!^! (! [! {! !
/p ! /strong ! /em ! break ! /<* ! /*> ! ec ! tag any
/br N ← N' ec CN
/br * N' ← S+/ S-/ S./ S:/ S. / S: / S#/ S^/ S (/ S {/ S [/ S /+/-/./:/. /: /#/^/ (/ {/ [
/br+S ←) / dq /, /] /} / !+!-!.!:!. !: !#!^! (! [! {! ec any
/br NSA ←. /:

function action(partno:int, R:seq.seq.byte, textOut:boolean) seq.byte
if partno = 2 then 1^R + X."+"
else if partno = 3 then 1^R + X."-"
else if partno = 4 then 1^R + X."."
else if partno = 5 then 1^R + X.":"
else if partno = 6 then 1^R + X.". "
else if partno = 7 then 1^R + X.": "
else if partno = 8 then 1^R + X."#"
else if partno = 9 then 1^R + X."^"
else if partno = 10 then addSpace.1^R
else if partno = 11 then 2^R + 1^R
else if partno = 12 then if textOut then linebreak.1^R else 1^R + X."<br>"
else if partno = 13 then block(2^R, 1^R, textOut)
else if partno = 14 then if textOut then 2^R + 1^R else 2^R + X."<table>" + 1^R + X."</table>"
else if partno = 15 then if textOut then paragraph.1^R else 1^R + X."<p>"
else if partno = 16 then 2^R + 1^R
else if partno = 17 then 2^R + 1^R + X."+"
else if partno = 18 then 2^R + 1^R + X."-"
else if partno = 19 then 2^R + 1^R + X."."
else if partno = 20 then 2^R + 1^R + X.":"
else if partno = 21 then 2^R + 1^R + X.". "
else if partno = 22 then 2^R + 1^R + X.": "
else if partno = 23 then 2^R + 1^R + X."#"
else if partno = 24 then 2^R + 1^R + X."^"
else if partno = 25 then 2^R + addSpace.1^R + X."("
else if partno = 26 then 2^R + addSpace.1^R + X."{"
else if partno = 27 then 2^R + addSpace.1^R + X."["
else if partno = 28 then 2^R + 1^R
else if partno = 29 then 1^R + X."+"
else if partno = 30 then 1^R + X."-"
else if partno = 31 then 1^R + X."."
else if partno = 32 then 1^R + X.":"
else if partno = 33 then 1^R + X.". "
else if partno = 34 then 1^R + X.": "
else if partno = 35 then 1^R + X."#"
else if partno = 36 then 1^R + X."^"
else if partno = 37 then 1^R + X."("
else if partno = 38 then 1^R + X."{"
else if partno = 39 then 1^R + X."["
else if partno = 40 then 1^R + X.")"
else if partno = 41 then 1^R + X.dq
else if partno = 42 then 1^R + X.","
else if partno = 43 then 1^R + X."]"
else if partno = 44 then 1^R + X."}"
else if partno = 45 then addSpace.2^R + (if textOut then 1^R else span(X."keyword", escape&<.1^R))
else if partno = 46 then
 addSpace.2^R
  + (if textOut then 1^R else X."<em>" + addSpace.escape&<.1^R + X."</em>")
else if partno = 47 then addSpace.2^R + (if textOut then 1^R else X."<em>" + escape&<.1^R + X."</em>")
else if partno = 48 then
 addSpace.2^R
  + (if textOut then 1^R else X."<strong>" + addSpace.escape&<.1^R + X."</strong>")
else if partno = 49 then
 addSpace.2^R
  + (if textOut then 1^R else X."<strong>" + escape&<.1^R + X."</strong>")
else if partno = 50 then if textOut then 1^R else 1^R + X."<td>"
else if partno = 51 then if textOut then 1^R + tobyte.10 else 1^R + X."<tr><td>"
else if partno = 52 then addSpace.3^R + (if textOut then 1^R else span(2^R, 1^R))
else if partno = 53 then addSpace.1^R
else if partno = 54 then addSpace.2^R + (if textOut then 1^R else escape&<.1^R)
else if partno = 55 then 2^R + 1^R
else if partno = 56 then 2^R + 1^R + X."+"
else if partno = 57 then 2^R + 1^R + X."-"
else if partno = 58 then 2^R + 1^R + X."."
else if partno = 59 then 2^R + 1^R + X.":"
else if partno = 60 then 2^R + 1^R + X.". "
else if partno = 61 then 2^R + 1^R + X.": "
else if partno = 62 then 2^R + 1^R + X."#"
else if partno = 63 then 2^R + 1^R + X."^"
else if partno = 64 then 2^R + addSpace.1^R + X."("
else if partno = 65 then 2^R + addSpace.1^R + X."{"
else if partno = 66 then 2^R + addSpace.1^R + X."["
else if partno = 67 then 2^R + 1^R
else if partno = 68 then 1^R + X."+"
else if partno = 69 then 1^R + X."-"
else if partno = 70 then 1^R + X."."
else if partno = 71 then 1^R + X.":"
else if partno = 72 then 1^R + X.". "
else if partno = 73 then 1^R + X.": "
else if partno = 74 then 1^R + X."#"
else if partno = 75 then 1^R + X."^"
else if partno = 76 then 1^R + X."("
else if partno = 77 then 1^R + X."{"
else if partno = 78 then 1^R + X."["
else if partno = 79 then 1^R + X.")"
else if partno = 80 then 1^R + X.dq
else if partno = 81 then 1^R + X.","
else if partno = 82 then 1^R + X."]"
else if partno = 83 then 1^R + X."}"
else if partno = 84 then addSpace.2^R + (if textOut then 1^R else escape&<.1^R)
else if partno = 85 then X.""
else if partno = 86 then X.""
else 1#R

function mytable seq.tableEntry
[
 {1} tableEntry(NT.T'.2, 1#"?", Match, Failure, "")
 , {2} tableEntry(T', 1#"+", Reduce*(2, T'.2), T'.3, "")
 , {3} tableEntry(T', 1#"-", Reduce*(3, T'.2), T'.4, "")
 , {4} tableEntry(T', 1#".", Reduce*(4, T'.2), T'.5, "")
 , {5} tableEntry(T', 1#":", Reduce*(5, T'.2), T'.6, "")
 , {6} tableEntry(T', 1#". ", Reduce*(6, T'.2), T'.7, "")
 , {7} tableEntry(T', 1#": ", Reduce*(7, T'.2), T'.8, "")
 , {8} tableEntry(T', 1#"#", Reduce*(8, T'.2), T'.9, "")
 , {9} tableEntry(T', 1#"^", Reduce*(9, T'.2), T'.10, "")
 , {10} tableEntry(T', 1#"/sp", Reduce*(10, T'.2), T.11, "")
 , {11} tableEntry(T, merge."/ ta g", !T.12, T'.14, "")
 , {12} tableEntry(!T, escapeformat, T'.14, MatchAny.13, "")
 , {13} tableEntry(MatchAny, 1#"?", Reduce*(11, T'.2), T'.14, "")
 , {14} tableEntry(T', 1#"/br", Reduce*(12, T'.2), T'.15, "")
 , {15} tableEntry(T', /<*, T'.16, T'.23, "")
 , {16} tableEntry(T', 1#"block", NT.17, T.20, "")
 , {17} tableEntry(NT.T'.2, 1#"CN", T.18, T'.19, "")
 , {18} tableEntry(T, /*>, Reduce*(13, T'.2), T'.19, "")
 , {19} tableEntry(T', /<*, T.20, T'.23, "")
 , {20} tableEntry(T, 1#"table", NT.21, T'.23, "")
 , {21} tableEntry(NT.T'.2, 1#"CN", T.22, T'.23, "")
 , {22} tableEntry(T, /*>, Reduce*(14, T'.2), T'.23, "")
 , {23} tableEntry(T', 1#"/p", Reduce*(15, T'.2), T'.24, "")
 , {24} tableEntry(T', escapeformat, NT.25, NT.26, "")
 , {25} tableEntry(NT.106, 1#"N", Reduce*(16, T'.2), NT.26, "")
 , {26} tableEntry(NT.T'.60, 1#"CS", T'.27, T'.49, "")
 , {27} tableEntry(T', 1#"+", Reduce*(17, T'.2), T'.29, "")
 , {28} tableEntry(NT.T'.60, 1#"CS", T'.29, T'.49, "")
 , {29} tableEntry(T', 1#"-", Reduce*(18, T'.2), T'.31, "")
 , {30} tableEntry(NT.T'.60, 1#"CS", T'.31, T'.49, "")
 , {31} tableEntry(T', 1#".", Reduce*(19, T'.2), T'.33, "")
 , {32} tableEntry(NT.T'.60, 1#"CS", T'.33, T'.49, "")
 , {33} tableEntry(T', 1#":", Reduce*(20, T'.2), T'.35, "")
 , {34} tableEntry(NT.T'.60, 1#"CS", T'.35, T'.49, "")
 , {35} tableEntry(T', 1#". ", Reduce*(21, T'.2), T'.37, "")
 , {36} tableEntry(NT.T'.60, 1#"CS", T'.37, T'.49, "")
 , {37} tableEntry(T', 1#": ", Reduce*(22, T'.2), T'.39, "")
 , {38} tableEntry(NT.T'.60, 1#"CS", T'.39, T'.49, "")
 , {39} tableEntry(T', 1#"#", Reduce*(23, T'.2), T'.41, "")
 , {40} tableEntry(NT.T'.60, 1#"CS", T'.41, T'.49, "")
 , {41} tableEntry(T', 1#"^", Reduce*(24, T'.2), T'.43, "")
 , {42} tableEntry(NT.T'.60, 1#"CS", T'.43, T'.49, "")
 , {43} tableEntry(T', 1#"(", Reduce*(25, T'.2), T'.45, "")
 , {44} tableEntry(NT.T'.60, 1#"CS", T'.45, T'.49, "")
 , {45} tableEntry(T', 1#"{", Reduce*(26, T'.2), T.47, "")
 , {46} tableEntry(NT.T'.60, 1#"CS", T.47, T'.49, "")
 , {47} tableEntry(T, 1#"[", Reduce*(27, T'.2), NT.48, "")
 , {48} tableEntry(NT.T'.60, 1#"CS", Reduce*(28, T'.2), T'.49, "")
 , {49} tableEntry(T', 1#"+", Reduce*(29, T'.2), T'.50, "")
 , {50} tableEntry(T', 1#"-", Reduce*(30, T'.2), T'.51, "")
 , {51} tableEntry(T', 1#".", Reduce*(31, T'.2), T'.52, "")
 , {52} tableEntry(T', 1#":", Reduce*(32, T'.2), T'.53, "")
 , {53} tableEntry(T', 1#". ", Reduce*(33, T'.2), T'.54, "")
 , {54} tableEntry(T', 1#": ", Reduce*(34, T'.2), T'.55, "")
 , {55} tableEntry(T', 1#"#", Reduce*(35, T'.2), T'.56, "")
 , {56} tableEntry(T', 1#"^", Reduce*(36, T'.2), T'.57, "")
 , {57} tableEntry(T', 1#"(", Reduce*(37, T'.2), T'.58, "")
 , {58} tableEntry(T', 1#"{", Reduce*(38, T'.2), T.59, "")
 , {59} tableEntry(T, 1#"[", Reduce*(39, T'.2), Success*, "")
 , {60} tableEntry(T', 1#")", Reduce*(40, T'.163), T'.61, "")
 , {61} tableEntry(T', 1#dq, Reduce*(41, T'.163), T'.62, "")
 , {62} tableEntry(T', 1#",", Reduce*(42, T'.163), T'.63, "")
 , {63} tableEntry(T', 1#"]", Reduce*(43, T'.163), T'.64, "")
 , {64} tableEntry(T', 1#"}", Reduce*(44, T'.163), T'.65, "")
 , {65} tableEntry(T', 1#"/keyword", MatchAny.66, T.67, "")
 , {66} tableEntry(MatchAny, 1#"?", Reduce*(45, T'.163), S'.T.72, "")
 , {67} tableEntry(T, 1#"/em", MatchAny.68, T'.70, "")
 , {68} tableEntry(MatchAny, 1#"?", !T.69, T'.70, "")
 , {69} tableEntry(!T, 1#". ", T'.70, Reduce*(46, T'.60), "")
 , {70} tableEntry(T', 1#"/em", MatchAny.71, T.72, "")
 , {71} tableEntry(MatchAny, 1#"?", Reduce*(47, T'.163), T'.77, "")
 , {72} tableEntry(T, 1#"/strong", MatchAny.73, T'.75, "")
 , {73} tableEntry(MatchAny, 1#"?", !T.74, T'.75, "")
 , {74} tableEntry(!T, 1#". ", T'.75, Reduce*(48, T'.60), "")
 , {75} tableEntry(T', 1#"/strong", MatchAny.76, T'.77, "")
 , {76} tableEntry(MatchAny, 1#"?", Reduce*(49, T'.163), T'.77, "")
 , {77} tableEntry(T', 1#"/cell", Reduce*(50, T'.163), T'.78, "")
 , {78} tableEntry(T', 1#"/row", Reduce*(51, T'.163), T.79, "")
 , {79} tableEntry(T, /<*, !T.80, T.85, "")
 , {80} tableEntry(!T, 1#"block", T.85, !T.81, "")
 , {81} tableEntry(!T, 1#"table", T.85, MatchAny.82, "")
 , {82} tableEntry(MatchAny, 1#"?", NT.83, T.85, "")
 , {83} tableEntry(NT.T'.2, 1#"CN", T.84, T.85, "")
 , {84} tableEntry(T, /*>, Reduce*(52, T'.163), T.85, "")
 , {85} tableEntry(T, 1#"/sp", Reduce*(53, T'.163), !T.86, "")
 , {86} tableEntry(!T, 1#"+", Fail, !T.87, "")
 , {87} tableEntry(!T, 1#"-", Fail, !T.88, "")
 , {88} tableEntry(!T, 1#".", Fail, !T.89, "")
 , {89} tableEntry(!T, 1#":", Fail, !T.90, "")
 , {90} tableEntry(!T, 1#". ", Fail, !T.91, "")
 , {91} tableEntry(!T, 1#": ", Fail, !T.92, "")
 , {92} tableEntry(!T, 1#"#", Fail, !T.93, "")
 , {93} tableEntry(!T, 1#"^", Fail, !T.94, "")
 , {94} tableEntry(!T, 1#"(", Fail, !T.95, "")
 , {95} tableEntry(!T, 1#"[", Fail, !T.96, "")
 , {96} tableEntry(!T, 1#"{", Fail, !T.97, "")
 , {97} tableEntry(!T, 1#"/p", Fail, !T.98, "")
 , {98} tableEntry(!T, 1#"/strong", Fail, !T.99, "")
 , {99} tableEntry(!T, 1#"/em", Fail, !T.100, "")
 , {100} tableEntry(!T, 1#"/br", Fail, !T.101, "")
 , {101} tableEntry(!T, /<*, Fail, !T.102, "")
 , {102} tableEntry(!T, /*>, Fail, !T.103, "")
 , {103} tableEntry(!T, escapeformat, Fail, !T.104, "")
 , {104} tableEntry(!T, merge."/ ta g", Fail, MatchAny.105, "")
 , {105} tableEntry(MatchAny, 1#"?", Reduce*(54, T'.163), Fail, "")
 , {106} tableEntry(NT.109, 1#"N'", T.107, Fail, "")
 , {107} tableEntry(T, escapeformat, NT.108, Fail, "")
 , {108} tableEntry(NT.T'.2, 1#"CN", Reduce.55, Fail, "")
 , {109} tableEntry(NT.T'.143, 1#"S", T'.110, T'.132, "")
 , {110} tableEntry(T', 1#"+", Reduce*(56, NT.109), T'.112, "")
 , {111} tableEntry(NT.T'.143, 1#"S", T'.112, T'.132, "")
 , {112} tableEntry(T', 1#"-", Reduce*(57, NT.109), T'.114, "")
 , {113} tableEntry(NT.T'.143, 1#"S", T'.114, T'.132, "")
 , {114} tableEntry(T', 1#".", Reduce*(58, NT.109), T'.116, "")
 , {115} tableEntry(NT.T'.143, 1#"S", T'.116, T'.132, "")
 , {116} tableEntry(T', 1#":", Reduce*(59, NT.109), T'.118, "")
 , {117} tableEntry(NT.T'.143, 1#"S", T'.118, T'.132, "")
 , {118} tableEntry(T', 1#". ", Reduce*(60, NT.109), T'.120, "")
 , {119} tableEntry(NT.T'.143, 1#"S", T'.120, T'.132, "")
 , {120} tableEntry(T', 1#": ", Reduce*(61, NT.109), T'.122, "")
 , {121} tableEntry(NT.T'.143, 1#"S", T'.122, T'.132, "")
 , {122} tableEntry(T', 1#"#", Reduce*(62, NT.109), T'.124, "")
 , {123} tableEntry(NT.T'.143, 1#"S", T'.124, T'.132, "")
 , {124} tableEntry(T', 1#"^", Reduce*(63, NT.109), T'.126, "")
 , {125} tableEntry(NT.T'.143, 1#"S", T'.126, T'.132, "")
 , {126} tableEntry(T', 1#"(", Reduce*(64, NT.109), T'.128, "")
 , {127} tableEntry(NT.T'.143, 1#"S", T'.128, T'.132, "")
 , {128} tableEntry(T', 1#"{", Reduce*(65, NT.109), T.130, "")
 , {129} tableEntry(NT.T'.143, 1#"S", T.130, T'.132, "")
 , {130} tableEntry(T, 1#"[", Reduce*(66, NT.109), NT.131, "")
 , {131} tableEntry(NT.T'.143, 1#"S", Reduce*(67, NT.109), T'.132, "")
 , {132} tableEntry(T', 1#"+", Reduce*(68, NT.109), T'.133, "")
 , {133} tableEntry(T', 1#"-", Reduce*(69, NT.109), T'.134, "")
 , {134} tableEntry(T', 1#".", Reduce*(70, NT.109), T'.135, "")
 , {135} tableEntry(T', 1#":", Reduce*(71, NT.109), T'.136, "")
 , {136} tableEntry(T', 1#". ", Reduce*(72, NT.109), T'.137, "")
 , {137} tableEntry(T', 1#": ", Reduce*(73, NT.109), T'.138, "")
 , {138} tableEntry(T', 1#"#", Reduce*(74, NT.109), T'.139, "")
 , {139} tableEntry(T', 1#"^", Reduce*(75, NT.109), T'.140, "")
 , {140} tableEntry(T', 1#"(", Reduce*(76, NT.109), T'.141, "")
 , {141} tableEntry(T', 1#"{", Reduce*(77, NT.109), T.142, "")
 , {142} tableEntry(T, 1#"[", Reduce*(78, NT.109), Success*, "")
 , {143} tableEntry(T', 1#")", Reduce*(79, T'.209), T'.144, "")
 , {144} tableEntry(T', 1#dq, Reduce*(80, T'.209), T'.145, "")
 , {145} tableEntry(T', 1#",", Reduce*(81, T'.209), T'.146, "")
 , {146} tableEntry(T', 1#"]", Reduce*(82, T'.209), T.147, "")
 , {147} tableEntry(T, 1#"}", Reduce*(83, T'.209), !T.148, "")
 , {148} tableEntry(!T, 1#"+", Fail, !T.149, "")
 , {149} tableEntry(!T, 1#"-", Fail, !T.150, "")
 , {150} tableEntry(!T, 1#".", Fail, !T.151, "")
 , {151} tableEntry(!T, 1#":", Fail, !T.152, "")
 , {152} tableEntry(!T, 1#". ", Fail, !T.153, "")
 , {153} tableEntry(!T, 1#": ", Fail, !T.154, "")
 , {154} tableEntry(!T, 1#"#", Fail, !T.155, "")
 , {155} tableEntry(!T, 1#"^", Fail, !T.156, "")
 , {156} tableEntry(!T, 1#"(", Fail, !T.157, "")
 , {157} tableEntry(!T, 1#"[", Fail, !T.158, "")
 , {158} tableEntry(!T, 1#"{", Fail, !T.159, "")
 , {159} tableEntry(!T, escapeformat, Fail, MatchAny.160, "")
 , {160} tableEntry(MatchAny, 1#"?", Reduce*(84, T'.209), Fail, "")
 , {161} tableEntry(T', 1#". ", Reduce.85, T.162, "")
 , {162} tableEntry(T, 1#":", Reduce.86, Fail, "")
 , {163} tableEntry(T', 1#")", Reduce*(40, T'.163), T'.164, "")
 , {164} tableEntry(T', 1#dq, Reduce*(41, T'.163), T'.165, "")
 , {165} tableEntry(T', 1#",", Reduce*(42, T'.163), T'.166, "")
 , {166} tableEntry(T', 1#"]", Reduce*(43, T'.163), T'.167, "")
 , {167} tableEntry(T', 1#"}", Reduce*(44, T'.163), T'.168, "")
 , {168} tableEntry(T', 1#"/keyword", MatchAny.169, T.170, "")
 , {169} tableEntry(MatchAny, 1#"?", Reduce*(45, T'.163), S'.T.72, "")
 , {170} tableEntry(T, 1#"/em", MatchAny.171, T'.173, "")
 , {171} tableEntry(MatchAny, 1#"?", !T.172, T'.173, "")
 , {172} tableEntry(!T, 1#". ", T'.173, Reduce*(46, T'.163), "")
 , {173} tableEntry(T', 1#"/em", MatchAny.174, T.175, "")
 , {174} tableEntry(MatchAny, 1#"?", Reduce*(47, T'.163), T'.77, "")
 , {175} tableEntry(T, 1#"/strong", MatchAny.176, T'.178, "")
 , {176} tableEntry(MatchAny, 1#"?", !T.177, T'.178, "")
 , {177} tableEntry(!T, 1#". ", T'.178, Reduce*(48, T'.163), "")
 , {178} tableEntry(T', 1#"/strong", MatchAny.179, T'.180, "")
 , {179} tableEntry(MatchAny, 1#"?", Reduce*(49, T'.163), T'.180, "")
 , {180} tableEntry(T', 1#"/cell", Reduce*(50, T'.163), T'.181, "")
 , {181} tableEntry(T', 1#"/row", Reduce*(51, T'.163), T.182, "")
 , {182} tableEntry(T, /<*, !T.183, T.188, "")
 , {183} tableEntry(!T, 1#"block", T.188, !T.184, "")
 , {184} tableEntry(!T, 1#"table", T.188, MatchAny.185, "")
 , {185} tableEntry(MatchAny, 1#"?", NT.186, T.188, "")
 , {186} tableEntry(NT.T'.2, 1#"CN", T.187, T.188, "")
 , {187} tableEntry(T, /*>, Reduce*(52, T'.163), T.188, "")
 , {188} tableEntry(T, 1#"/sp", Reduce*(53, T'.163), !T.189, "")
 , {189} tableEntry(!T, 1#"+", Success*, !T.190, "")
 , {190} tableEntry(!T, 1#"-", Success*, !T.191, "")
 , {191} tableEntry(!T, 1#".", Success*, !T.192, "")
 , {192} tableEntry(!T, 1#":", Success*, !T.193, "")
 , {193} tableEntry(!T, 1#". ", Success*, !T.194, "")
 , {194} tableEntry(!T, 1#": ", Success*, !T.195, "")
 , {195} tableEntry(!T, 1#"#", Success*, !T.196, "")
 , {196} tableEntry(!T, 1#"^", Success*, !T.197, "")
 , {197} tableEntry(!T, 1#"(", Success*, !T.198, "")
 , {198} tableEntry(!T, 1#"[", Success*, !T.199, "")
 , {199} tableEntry(!T, 1#"{", Success*, !T.200, "")
 , {200} tableEntry(!T, 1#"/p", Success*, !T.201, "")
 , {201} tableEntry(!T, 1#"/strong", Success*, !T.202, "")
 , {202} tableEntry(!T, 1#"/em", Success*, !T.203, "")
 , {203} tableEntry(!T, 1#"/br", Success*, !T.204, "")
 , {204} tableEntry(!T, /<*, Success*, !T.205, "")
 , {205} tableEntry(!T, /*>, Success*, !T.206, "")
 , {206} tableEntry(!T, escapeformat, Success*, !T.207, "")
 , {207} tableEntry(!T, merge."/ ta g", Success*, MatchAny.208, "")
 , {208} tableEntry(MatchAny, 1#"?", Reduce*(54, T'.163), Success*, "")
 , {209} tableEntry(T', 1#")", Reduce*(79, T'.209), T'.210, "")
 , {210} tableEntry(T', 1#dq, Reduce*(80, T'.209), T'.211, "")
 , {211} tableEntry(T', 1#",", Reduce*(81, T'.209), T'.212, "")
 , {212} tableEntry(T', 1#"]", Reduce*(82, T'.209), T.213, "")
 , {213} tableEntry(T, 1#"}", Reduce*(83, T'.209), !T.214, "")
 , {214} tableEntry(!T, 1#"+", Success*, !T.215, "")
 , {215} tableEntry(!T, 1#"-", Success*, !T.216, "")
 , {216} tableEntry(!T, 1#".", Success*, !T.217, "")
 , {217} tableEntry(!T, 1#":", Success*, !T.218, "")
 , {218} tableEntry(!T, 1#". ", Success*, !T.219, "")
 , {219} tableEntry(!T, 1#": ", Success*, !T.220, "")
 , {220} tableEntry(!T, 1#"#", Success*, !T.221, "")
 , {221} tableEntry(!T, 1#"^", Success*, !T.222, "")
 , {222} tableEntry(!T, 1#"(", Success*, !T.223, "")
 , {223} tableEntry(!T, 1#"[", Success*, !T.224, "")
 , {224} tableEntry(!T, 1#"{", Success*, !T.225, "")
 , {225} tableEntry(!T, escapeformat, Success*, MatchAny.226, "")
 , {226} tableEntry(MatchAny, 1#"?", Reduce*(84, T'.209), Success*, "")
]

function =(seq.word, seq.byte) boolean true

function $(int) seq.byte 1#empty:seq.seq.byte

use standard

use seq.tableEntry

use otherseq.frame

use stack.frame

use otherseq.seq.byte

use PEGrules

function place(r:thisresult) int i.top.stk.r

type frame is
Sstate:state
, Fstate:state
, i:int
, result:seq.seq.byte
, faili:int
, failresult:seq.seq.byte

type thisresult is stk:stack.frame

Function status(a:thisresult) word
if Sstate.top.stk.a ≠ Match then 1#"Failed"
else if place.a = {length of input} faili.top.stk.a then 1#"Match"
else 1#"MatchPrefix"

Function result(a:thisresult) seq.byte 1^result.top.stk.a

function parse(myinput0:seq.word, initAttr:seq.byte, textOut:boolean) thisresult
let myinput = packed(myinput0 + endMark)
let packedTable = packed.mytable
for
 stk = empty:stack.frame
 , state = startstate
 , i = 1
 , inputi = 1#myinput
 , result = [initAttr]
 , faili = 1
 , failresult = [initAttr]
while toint.state > toint.Match
do
 let actionState = action.state,
 if actionState = Fail then
  {goto Fstate.top.stk, i = faili.top, pop.stk, discard result}
  let top = top.stk,
  if toint.action.Fstate.top ≥ toint.S' then
   let newi = i.top,
   next(
    pop.stk
    , nextState.Fstate.top
    , newi
    , idxNB(myinput, newi)
    , result.top
    , faili.top
    , failresult.top
   )
  else
   next(
    pop.stk
    , Fstate.top
    , faili.top
    , idxNB(myinput, faili.top)
    , failresult.top
    , faili.top
    , failresult.top
   )
 else if actionState = Success* then
  {goto Sstate.top.stk, pop.stk, keep result}
  let top = top.stk,
  next(pop.stk, Sstate.top, i, inputi, result.top + result, faili.top, failresult.top)
 else if actionState = Discard* then
  let top = top.stk,
  next(stk, nextState.state, i, inputi, result.top, i, result.top)
 else if actionState = All then
  let top = top.stk
  let att = [toAttribute(1^result, subseq(myinput, i.top, i - 1))],
  next(pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
 else if actionState = Lambda then
  let att = [action(reduceNo.state, result, textOut)],
  next(stk, nextState2.state, i, inputi, result + att, faili, failresult)
 else if actionState = Reduce then
  let top = top.stk
  let att = [action(reduceNo.state, result, textOut)],
  next(pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
 else if actionState = Reduce* then
  let att = [action(reduceNo.state, result, textOut)]
  let top = top.stk,
  next(stk, nextState.state, i, inputi, att, i, att)
 else if actionState = !Reduce then
  let top = top.stk
  let ini = idxNB(myinput, faili.top),
  next(pop.stk, Fstate.top, faili.top, ini, failresult.top, faili.top, failresult.top)
 else if actionState = !Fail then
  let top = top.stk
  let ini = idxNB(myinput, i.top),
  next(pop.stk, Sstate.top, i.top, ini, result.top, faili.top, failresult.top)
 else if actionState = T then
  let te = idxNB(packedTable, index.state),
  if inputi ≠ match.te then {fail} next(stk, Fstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
  else next(stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
 else if actionState = !T then
  let te = idxNB(packedTable, index.state),
  if inputi = match.te then {fail} next(stk, Sstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
  else next(stk, Fstate.te, i, inputi, result, faili, failresult)
 else if actionState = MatchAny then
  let te = idxNB(packedTable, index.state),
  if inputi = endMark then {fail} next(stk, Fstate.te, i, inputi, result, faili, failresult)
  else
   let reslt = result + toAttribute(1^result, [inputi])
   let ini = idxNB(myinput, i + 1),
   next(stk, Sstate.te, i + 1, ini, reslt, faili, failresult)
 else if actionState = T' then
  let te = idxNB(packedTable, index.state),
  if inputi = match.te then next(stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
  else next(stk, Fstate.te, i, inputi, result, faili, failresult)
 else
  {match non Terminal}
  let te = idxNB(packedTable, index.state)
  assert action.action.te ∈ [NT, NT*] report "PROBLEM PEG^(state)"
  let newstk = push(stk, frame(Sstate.te, Fstate.te, i, result, faili, failresult)),
  let tmp = [toAttribute(1^result, empty:seq.word)],
  next(newstk, nextState.action.te, i, inputi, tmp, i, tmp),
thisresult.push(stk, frame(state, state, i, result, n.myinput, result)) 