Module format1

use PEGrules

use UTF8

use bits

use seq1.byte

use seq.seq.byte

use stack.frame

use seq1.int

use set.int

use standard

use seq.tableEntry

use seq.word

use seq1.seq.word

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
 + (if a sub i = amp then X."&amp;" else X."&lt;")
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
X."<span" + tobyte.32 + X."class" + X."=" + class + X.">" + b + X."</span>"

function addSpace(a:seq.byte) seq.byte
if isempty.a ∨ a sub n.a = tobyte.32 then a else a + tobyte.32

function block(R0:seq.byte, R1:seq.byte, text:boolean) seq.byte
if isempty.R1 then R0
else if text then
 let body = if R1 sub n.R1 = tobyte.10 then R1 >> 1 else R1
 let init =
  linebreak.R0
  + if subseq(body, 1, 1) = [tobyte.32] then empty:seq.byte else [tobyte.32],
 for acc = init, b ∈ body do if b = tobyte.10 then acc + b + tobyte.32 else acc + b,
 linebreak.acc
else R0 + span(X."block", R1)

function paragraph(a:seq.byte) seq.byte
{used for text and not html}
a
 + if isempty.a ∨ a sub n.a ≠ tobyte.10 then [tobyte.10] + tobyte.10 else [tobyte.10]

function linebreak(a:seq.byte) seq.byte
{used for text and not html}
if isempty.a ∨ a sub n.a ≠ tobyte.10 then a + [tobyte.10] else a

CN process commands with no space pending

CS process commands with space pending

N no commands with no space pending

S no commands with space pending

NSBA no space before or after

NSB no space before

function endMark word encodeword.[char.254]

function break word "/br" sub 1

function /<* word "<* m *>" sub 1

function /*> word "<* m *>" sub 3

function genPEG(
seqElementType:word
, attributeType:seq.byte
, resultType:thisresult
, textOut:boolean
, commonType:boolean
) seq.boolean
{commonName: textOut notablex: wordmap: dq dq sub 1, ec escapeformat, tag merge."/ ta g", break"/br
"sub 1, /<* /<*, /*> /*>,"$"sub 1}
[
 "* CN+" = $.0 + X."+"
 , "/-" = $.0 + X."-"
 , "/." = $.0 + X."."
 , "/:" = $.0 + X.":"
 , "/. " = $.0 + X.". "
 , "/: " = $.0 + X.": "
 , "/ /sp" = addSpace.$.0
 , "/ /nsp" = $.0
 , "/ tag ! ec any" = $.0 + $.1
 , "/ break" = (if textOut then linebreak.$.0 else $.0 + X."<br>")
 , "/ /<* block CN /*>" = block($.0, $.1, textOut)
 , "/ /<* table CN /*>"
 = (if textOut then $.0 + $.1 else $.0 + X."<table>" + $.1 + X."</table>")
 , "/ /p"
 = (if textOut then paragraph.$.0
 else $.0 + X([encodeword.[char.10, char.10]] + "<p>"))
 , "/ ec N" = $.0 + $.1
 , "/ CS(" = $.0 + addSpace.$.1 + X."("
 , "/ CS{" = $.0 + addSpace.$.1 + X."{"
 , "/ CS[" = $.0 + addSpace.$.1 + X."["
 , "/ CS" = $.0 + $.1
 , "/(" = $.0 + X."("
 , "/{" = $.0 + X."{"
 , "/[" = $.0 + X."["
 , "+CS)" = $.0 + X.")"
 , "/ dq" = $.0 + X.dq
 , "/," = $.0 + X.","
 , "/]" = $.0 + X."]"
 , "/}" = $.0 + X."}"
 , "/ /keyword any"
 = addSpace.$.0 + (if textOut then $.1 else span(X."keyword", escape&<.$.1))
 , "/ /<* ! block ! table any CN /*>"
 = addSpace.$.0 + (if textOut then $.2 else span($.1, $.2))
 , "/ /sp" = addSpace.$.0
 , "/ !+!-!.!:!. !: !(![!{! ! /p ! break ! /<* ! /*> ! ec ! tag ! /nsp any"
 = addSpace.$.0 + (if textOut then $.1 else escape&<.$.1)
 , "N N' ec CN" = $.1 + $.2
 , "* N' S+" = $.0 + $.1 + X."+"
 , "/ S-" = $.0 + $.1 + X."-"
 , "/ S." = $.0 + $.1 + X."."
 , "/ S:" = $.0 + $.1 + X.":"
 , "/ S. " = $.0 + $.1 + X.". "
 , "/ S: " = $.0 + $.1 + X.": "
 , "/ S(" = $.0 + addSpace.$.1 + X."("
 , "/ S{" = $.0 + addSpace.$.1 + X."{"
 , "/ S[" = $.0 + addSpace.$.1 + X."["
 , "/ S" = $.0 + $.1
 , "/+" = $.0 + X."+"
 , "/-" = $.0 + X."-"
 , "/." = $.0 + X."."
 , "/:" = $.0 + X.":"
 , "/. " = $.0 + X.". "
 , "/: " = $.0 + X.": "
 , "/(" = $.0 + X."("
 , "/{" = $.0 + X."{"
 , "/[" = $.0 + X."["
 , "+S)" = $.0 + X.")"
 , "/ dq" = $.0 + X.dq
 , "/," = $.0 + X.","
 , "/]" = $.0 + X."]"
 , "/}" = $.0 + X."}"
 , "/ !+!-!.!:!. !: !(![!{! ec any"
 = addSpace.$.0 + if textOut then $.1 else escape&<.$.1
]

<<<< Below is auto generated code >>>>

/br Non-terminals:CN CS N N' S /br
Terminals:()+,-.. /*> /<* /keyword /nsp /p
/sp:: []any block break dq ec table tag{}/br
* CN ←+/-/./:/. /: / /sp / /nsp / tag ! ec any / break / /<* block CN /*> / /<* table CN /*> / /p
/ ec N / CS(/ CS{/ CS[/ CS /(/{/[/br
+CS ←)/ dq /, /]/}/ /keyword any / /<* ! block ! table any CN /*> / /sp / !+!-!.!:!. !: !(![!{! ! /p
! break ! /<* ! /*> ! ec ! tag ! /nsp any /br
N ← N' ec CN /br
* N' ← S+/ S-/ S./ S:/ S. / S: / S(/ S{/ S[/ S /+/-/./:/. /: /(/{/[/br
+S ←)/ dq /, /]/}/ !+!-!.!:!. !: !(![!{! ec any

function action(partno:int, R:seq.seq.byte, textOut:boolean) seq.byte
if partno = 2 then R sub n.R + X."+"
else if partno = 3 then R sub n.R + X."-"
else if partno = 4 then R sub n.R + X."."
else if partno = 5 then R sub n.R + X.":"
else if partno = 6 then R sub n.R + X.". "
else if partno = 7 then R sub n.R + X.": "
else if partno = 8 then addSpace.R sub n.R
else if partno = 9 then R sub n.R
else if partno = 10 then R sub (n.R - 1) + R sub n.R
else if partno = 11 then if textOut then linebreak.R sub n.R else R sub n.R + X."<br>"
else if partno = 12 then block(R sub (n.R - 1), R sub n.R, textOut)
else if partno = 13 then
 if textOut then R sub (n.R - 1) + R sub n.R
 else R sub (n.R - 1) + X."<table>" + R sub n.R + X."</table>"
else if partno = 14 then
 if textOut then paragraph.R sub n.R
 else R sub n.R + X([encodeword.[char.10, char.10]] + "<p>")
else if partno = 15 then R sub (n.R - 1) + R sub n.R
else if partno = 16 then R sub (n.R - 1) + addSpace.R sub n.R + X."("
else if partno = 17 then R sub (n.R - 1) + addSpace.R sub n.R + X."{"
else if partno = 18 then R sub (n.R - 1) + addSpace.R sub n.R + X."["
else if partno = 19 then R sub (n.R - 1) + R sub n.R
else if partno = 20 then R sub n.R + X."("
else if partno = 21 then R sub n.R + X."{"
else if partno = 22 then R sub n.R + X."["
else if partno = 23 then R sub n.R + X.")"
else if partno = 24 then R sub n.R + X.dq
else if partno = 25 then R sub n.R + X.","
else if partno = 26 then R sub n.R + X."]"
else if partno = 27 then R sub n.R + X."}"
else if partno = 28 then
 addSpace.R sub (n.R - 1)
 + if textOut then R sub n.R else span(X."keyword", escape&<.R sub n.R)
else if partno = 29 then
 addSpace.R sub (n.R - 2)
 + if textOut then R sub n.R else span(R sub (n.R - 1), R sub n.R)
else if partno = 30 then addSpace.R sub n.R
else if partno = 31 then addSpace.R sub (n.R - 1) + if textOut then R sub n.R else escape&<.R sub n.R
else if partno = 32 then R sub (n.R - 1) + R sub n.R
else if partno = 33 then R sub (n.R - 1) + R sub n.R + X."+"
else if partno = 34 then R sub (n.R - 1) + R sub n.R + X."-"
else if partno = 35 then R sub (n.R - 1) + R sub n.R + X."."
else if partno = 36 then R sub (n.R - 1) + R sub n.R + X.":"
else if partno = 37 then R sub (n.R - 1) + R sub n.R + X.". "
else if partno = 38 then R sub (n.R - 1) + R sub n.R + X.": "
else if partno = 39 then R sub (n.R - 1) + addSpace.R sub n.R + X."("
else if partno = 40 then R sub (n.R - 1) + addSpace.R sub n.R + X."{"
else if partno = 41 then R sub (n.R - 1) + addSpace.R sub n.R + X."["
else if partno = 42 then R sub (n.R - 1) + R sub n.R
else if partno = 43 then R sub n.R + X."+"
else if partno = 44 then R sub n.R + X."-"
else if partno = 45 then R sub n.R + X."."
else if partno = 46 then R sub n.R + X.":"
else if partno = 47 then R sub n.R + X.". "
else if partno = 48 then R sub n.R + X.": "
else if partno = 49 then R sub n.R + X."("
else if partno = 50 then R sub n.R + X."{"
else if partno = 51 then R sub n.R + X."["
else if partno = 52 then R sub n.R + X.")"
else if partno = 53 then R sub n.R + X.dq
else if partno = 54 then R sub n.R + X.","
else if partno = 55 then R sub n.R + X."]"
else if partno = 56 then R sub n.R + X."}"
else if partno = 57 then addSpace.R sub (n.R - 1) + if textOut then R sub n.R else escape&<.R sub n.R
else R sub 1

function mytable seq.tableEntry
[
 {1}tableEntry(NT.T'.2, "?" sub 1, Match, Failure, "")
 , {2}tableEntry(T', "+" sub 1, Reduce*(2, T'.2), T'.3, "")
 , {3}tableEntry(T', "-" sub 1, Reduce*(3, T'.2), T'.4, "")
 , {4}tableEntry(T', "." sub 1, Reduce*(4, T'.2), T'.5, "")
 , {5}tableEntry(T', ":" sub 1, Reduce*(5, T'.2), T'.6, "")
 , {6}tableEntry(T', ". " sub 1, Reduce*(6, T'.2), T'.7, "")
 , {7}tableEntry(T', ": " sub 1, Reduce*(7, T'.2), T'.8, "")
 , {8}tableEntry(T', "/sp" sub 1, Reduce*(8, T'.2), T'.9, "")
 , {9}tableEntry(T', "/nsp" sub 1, Reduce*(9, T'.2), T.10, "")
 , {10}tableEntry(T, merge."/ ta g", !T.11, T'.13, "")
 , {11}tableEntry(!T, escapeformat, T'.13, MatchAny.12, "")
 , {12}tableEntry(MatchAny, "?" sub 1, Reduce*(10, T'.2), T'.13, "")
 , {13}tableEntry(T', "/br" sub 1, Reduce*(11, T'.2), T'.14, "")
 , {14}tableEntry(T', /<*, T'.15, T'.22, "")
 , {15}tableEntry(T', "block" sub 1, NT.16, T.19, "")
 , {16}tableEntry(NT.T'.2, "CN" sub 1, T.17, T'.18, "")
 , {17}tableEntry(T, /*>, Reduce*(12, T'.2), T'.18, "")
 , {18}tableEntry(T', /<*, T.19, T'.22, "")
 , {19}tableEntry(T, "table" sub 1, NT.20, T'.22, "")
 , {20}tableEntry(NT.T'.2, "CN" sub 1, T.21, T'.22, "")
 , {21}tableEntry(T, /*>, Reduce*(13, T'.2), T'.22, "")
 , {22}tableEntry(T', "/p" sub 1, Reduce*(14, T'.2), T'.23, "")
 , {23}tableEntry(T', escapeformat, NT.24, NT.25, "")
 , {24}tableEntry(NT.66, "N" sub 1, Reduce*(15, T'.2), NT.25, "")
 , {25}tableEntry(NT.T'.35, "CS" sub 1, T'.26, T'.32, "")
 , {26}tableEntry(T', "(" sub 1, Reduce*(16, T'.2), T'.28, "")
 , {27}tableEntry(NT.T'.35, "CS" sub 1, T'.28, T'.32, "")
 , {28}tableEntry(T', "{" sub 1, Reduce*(17, T'.2), T.30, "")
 , {29}tableEntry(NT.T'.35, "CS" sub 1, T.30, T'.32, "")
 , {30}tableEntry(T, "[" sub 1, Reduce*(18, T'.2), NT.31, "")
 , {31}tableEntry(NT.T'.35, "CS" sub 1, Reduce*(19, T'.2), T'.32, "")
 , {32}tableEntry(T', "(" sub 1, Reduce*(20, T'.2), T'.33, "")
 , {33}tableEntry(T', "{" sub 1, Reduce*(21, T'.2), T.34, "")
 , {34}tableEntry(T, "[" sub 1, Reduce*(22, T'.2), Success*, "")
 , {35}tableEntry(T', ")" sub 1, Reduce*(23, T'.113), T'.36, "")
 , {36}tableEntry(T', dq sub 1, Reduce*(24, T'.113), T'.37, "")
 , {37}tableEntry(T', "," sub 1, Reduce*(25, T'.113), T'.38, "")
 , {38}tableEntry(T', "]" sub 1, Reduce*(26, T'.113), T'.39, "")
 , {39}tableEntry(T', "}" sub 1, Reduce*(27, T'.113), T'.40, "")
 , {40}tableEntry(T', "/keyword" sub 1, MatchAny.41, T.42, "")
 , {41}tableEntry(MatchAny, "?" sub 1, Reduce*(28, T'.113), T.42, "")
 , {42}tableEntry(T, /<*, !T.43, T.48, "")
 , {43}tableEntry(!T, "block" sub 1, T.48, !T.44, "")
 , {44}tableEntry(!T, "table" sub 1, T.48, MatchAny.45, "")
 , {45}tableEntry(MatchAny, "?" sub 1, NT.46, T.48, "")
 , {46}tableEntry(NT.T'.2, "CN" sub 1, T.47, T.48, "")
 , {47}tableEntry(T, /*>, Reduce*(29, T'.113), T.48, "")
 , {48}tableEntry(T, "/sp" sub 1, Reduce*(30, T'.113), !T.49, "")
 , {49}tableEntry(!T, "+" sub 1, Fail, !T.50, "")
 , {50}tableEntry(!T, "-" sub 1, Fail, !T.51, "")
 , {51}tableEntry(!T, "." sub 1, Fail, !T.52, "")
 , {52}tableEntry(!T, ":" sub 1, Fail, !T.53, "")
 , {53}tableEntry(!T, ". " sub 1, Fail, !T.54, "")
 , {54}tableEntry(!T, ": " sub 1, Fail, !T.55, "")
 , {55}tableEntry(!T, "(" sub 1, Fail, !T.56, "")
 , {56}tableEntry(!T, "[" sub 1, Fail, !T.57, "")
 , {57}tableEntry(!T, "{" sub 1, Fail, !T.58, "")
 , {58}tableEntry(!T, "/p" sub 1, Fail, !T.59, "")
 , {59}tableEntry(!T, "/br" sub 1, Fail, !T.60, "")
 , {60}tableEntry(!T, /<*, Fail, !T.61, "")
 , {61}tableEntry(!T, /*>, Fail, !T.62, "")
 , {62}tableEntry(!T, escapeformat, Fail, !T.63, "")
 , {63}tableEntry(!T, merge."/ ta g", Fail, !T.64, "")
 , {64}tableEntry(!T, "/nsp" sub 1, Fail, MatchAny.65, "")
 , {65}tableEntry(MatchAny, "?" sub 1, Reduce*(31, T'.113), Fail, "")
 , {66}tableEntry(NT.69, "N'" sub 1, T.67, Fail, "")
 , {67}tableEntry(T, escapeformat, NT.68, Fail, "")
 , {68}tableEntry(NT.T'.2, "CN" sub 1, Reduce.32, Fail, "")
 , {69}tableEntry(NT.T'.97, "S" sub 1, T'.70, T'.88, "")
 , {70}tableEntry(T', "+" sub 1, Reduce*(33, NT.69), T'.72, "")
 , {71}tableEntry(NT.T'.97, "S" sub 1, T'.72, T'.88, "")
 , {72}tableEntry(T', "-" sub 1, Reduce*(34, NT.69), T'.74, "")
 , {73}tableEntry(NT.T'.97, "S" sub 1, T'.74, T'.88, "")
 , {74}tableEntry(T', "." sub 1, Reduce*(35, NT.69), T'.76, "")
 , {75}tableEntry(NT.T'.97, "S" sub 1, T'.76, T'.88, "")
 , {76}tableEntry(T', ":" sub 1, Reduce*(36, NT.69), T'.78, "")
 , {77}tableEntry(NT.T'.97, "S" sub 1, T'.78, T'.88, "")
 , {78}tableEntry(T', ". " sub 1, Reduce*(37, NT.69), T'.80, "")
 , {79}tableEntry(NT.T'.97, "S" sub 1, T'.80, T'.88, "")
 , {80}tableEntry(T', ": " sub 1, Reduce*(38, NT.69), T'.82, "")
 , {81}tableEntry(NT.T'.97, "S" sub 1, T'.82, T'.88, "")
 , {82}tableEntry(T', "(" sub 1, Reduce*(39, NT.69), T'.84, "")
 , {83}tableEntry(NT.T'.97, "S" sub 1, T'.84, T'.88, "")
 , {84}tableEntry(T', "{" sub 1, Reduce*(40, NT.69), T.86, "")
 , {85}tableEntry(NT.T'.97, "S" sub 1, T.86, T'.88, "")
 , {86}tableEntry(T, "[" sub 1, Reduce*(41, NT.69), NT.87, "")
 , {87}tableEntry(NT.T'.97, "S" sub 1, Reduce*(42, NT.69), T'.88, "")
 , {88}tableEntry(T', "+" sub 1, Reduce*(43, NT.69), T'.89, "")
 , {89}tableEntry(T', "-" sub 1, Reduce*(44, NT.69), T'.90, "")
 , {90}tableEntry(T', "." sub 1, Reduce*(45, NT.69), T'.91, "")
 , {91}tableEntry(T', ":" sub 1, Reduce*(46, NT.69), T'.92, "")
 , {92}tableEntry(T', ". " sub 1, Reduce*(47, NT.69), T'.93, "")
 , {93}tableEntry(T', ": " sub 1, Reduce*(48, NT.69), T'.94, "")
 , {94}tableEntry(T', "(" sub 1, Reduce*(49, NT.69), T'.95, "")
 , {95}tableEntry(T', "{" sub 1, Reduce*(50, NT.69), T.96, "")
 , {96}tableEntry(T, "[" sub 1, Reduce*(51, NT.69), Success*, "")
 , {97}tableEntry(T', ")" sub 1, Reduce*(52, T'.144), T'.98, "")
 , {98}tableEntry(T', dq sub 1, Reduce*(53, T'.144), T'.99, "")
 , {99}tableEntry(T', "," sub 1, Reduce*(54, T'.144), T'.100, "")
 , {100}tableEntry(T', "]" sub 1, Reduce*(55, T'.144), T.101, "")
 , {101}tableEntry(T, "}" sub 1, Reduce*(56, T'.144), !T.102, "")
 , {102}tableEntry(!T, "+" sub 1, Fail, !T.103, "")
 , {103}tableEntry(!T, "-" sub 1, Fail, !T.104, "")
 , {104}tableEntry(!T, "." sub 1, Fail, !T.105, "")
 , {105}tableEntry(!T, ":" sub 1, Fail, !T.106, "")
 , {106}tableEntry(!T, ". " sub 1, Fail, !T.107, "")
 , {107}tableEntry(!T, ": " sub 1, Fail, !T.108, "")
 , {108}tableEntry(!T, "(" sub 1, Fail, !T.109, "")
 , {109}tableEntry(!T, "[" sub 1, Fail, !T.110, "")
 , {110}tableEntry(!T, "{" sub 1, Fail, !T.111, "")
 , {111}tableEntry(!T, escapeformat, Fail, MatchAny.112, "")
 , {112}tableEntry(MatchAny, "?" sub 1, Reduce*(57, T'.144), Fail, "")
 , {113}tableEntry(T', ")" sub 1, Reduce*(23, T'.113), T'.114, "")
 , {114}tableEntry(T', dq sub 1, Reduce*(24, T'.113), T'.115, "")
 , {115}tableEntry(T', "," sub 1, Reduce*(25, T'.113), T'.116, "")
 , {116}tableEntry(T', "]" sub 1, Reduce*(26, T'.113), T'.117, "")
 , {117}tableEntry(T', "}" sub 1, Reduce*(27, T'.113), T'.118, "")
 , {118}tableEntry(T', "/keyword" sub 1, MatchAny.119, T.120, "")
 , {119}tableEntry(MatchAny, "?" sub 1, Reduce*(28, T'.113), T.120, "")
 , {120}tableEntry(T, /<*, !T.121, T.126, "")
 , {121}tableEntry(!T, "block" sub 1, T.126, !T.122, "")
 , {122}tableEntry(!T, "table" sub 1, T.126, MatchAny.123, "")
 , {123}tableEntry(MatchAny, "?" sub 1, NT.124, T.126, "")
 , {124}tableEntry(NT.T'.2, "CN" sub 1, T.125, T.126, "")
 , {125}tableEntry(T, /*>, Reduce*(29, T'.113), T.126, "")
 , {126}tableEntry(T, "/sp" sub 1, Reduce*(30, T'.113), !T.127, "")
 , {127}tableEntry(!T, "+" sub 1, Success*, !T.128, "")
 , {128}tableEntry(!T, "-" sub 1, Success*, !T.129, "")
 , {129}tableEntry(!T, "." sub 1, Success*, !T.130, "")
 , {130}tableEntry(!T, ":" sub 1, Success*, !T.131, "")
 , {131}tableEntry(!T, ". " sub 1, Success*, !T.132, "")
 , {132}tableEntry(!T, ": " sub 1, Success*, !T.133, "")
 , {133}tableEntry(!T, "(" sub 1, Success*, !T.134, "")
 , {134}tableEntry(!T, "[" sub 1, Success*, !T.135, "")
 , {135}tableEntry(!T, "{" sub 1, Success*, !T.136, "")
 , {136}tableEntry(!T, "/p" sub 1, Success*, !T.137, "")
 , {137}tableEntry(!T, "/br" sub 1, Success*, !T.138, "")
 , {138}tableEntry(!T, /<*, Success*, !T.139, "")
 , {139}tableEntry(!T, /*>, Success*, !T.140, "")
 , {140}tableEntry(!T, escapeformat, Success*, !T.141, "")
 , {141}tableEntry(!T, merge."/ ta g", Success*, !T.142, "")
 , {142}tableEntry(!T, "/nsp" sub 1, Success*, MatchAny.143, "")
 , {143}tableEntry(MatchAny, "?" sub 1, Reduce*(31, T'.113), Success*, "")
 , {144}tableEntry(T', ")" sub 1, Reduce*(52, T'.144), T'.145, "")
 , {145}tableEntry(T', dq sub 1, Reduce*(53, T'.144), T'.146, "")
 , {146}tableEntry(T', "," sub 1, Reduce*(54, T'.144), T'.147, "")
 , {147}tableEntry(T', "]" sub 1, Reduce*(55, T'.144), T.148, "")
 , {148}tableEntry(T, "}" sub 1, Reduce*(56, T'.144), !T.149, "")
 , {149}tableEntry(!T, "+" sub 1, Success*, !T.150, "")
 , {150}tableEntry(!T, "-" sub 1, Success*, !T.151, "")
 , {151}tableEntry(!T, "." sub 1, Success*, !T.152, "")
 , {152}tableEntry(!T, ":" sub 1, Success*, !T.153, "")
 , {153}tableEntry(!T, ". " sub 1, Success*, !T.154, "")
 , {154}tableEntry(!T, ": " sub 1, Success*, !T.155, "")
 , {155}tableEntry(!T, "(" sub 1, Success*, !T.156, "")
 , {156}tableEntry(!T, "[" sub 1, Success*, !T.157, "")
 , {157}tableEntry(!T, "{" sub 1, Success*, !T.158, "")
 , {158}tableEntry(!T, escapeformat, Success*, MatchAny.159, "")
 , {159}tableEntry(MatchAny, "?" sub 1, Reduce*(57, T'.144), Success*, "")
]

function =(seq.word, seq.byte) boolean true

function $(int) seq.byte empty:seq.seq.byte sub 1

use standard

use seq.tableEntry

use seq1.frame

use stack.frame

use seq1.seq.byte

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
if Sstate.top.stk.a ≠ Match then 'Failed
else if place.a = {length of input}faili.top.stk.a then 'Match
else 'MatchPrefix

Function result(a:thisresult) seq.byte
let t = result.top.stk.a,
t sub n.t

function parse(myinput0:seq.word, initAttr:seq.byte, textOut:boolean) thisresult
let myinput = packed(myinput0 + endMark)
let packedTable = packed.mytable
for
 stk = empty:stack.frame
 , state = startstate
 , i = 1
 , inputi = myinput sub 1
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
  let att = [toAttribute(result sub n.result, subseq(myinput, i.top, i - 1))],
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
  if inputi ≠ match.te then{fail}next(stk, Fstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
  else next(stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
 else if actionState = !T then
  let te = idxNB(packedTable, index.state),
  if inputi = match.te then{fail}next(stk, Sstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
  else next(stk, Fstate.te, i, inputi, result, faili, failresult)
 else if actionState = MatchAny then
  let te = idxNB(packedTable, index.state),
  if inputi = endMark then {fail}next(stk, Fstate.te, i, inputi, result, faili, failresult)
  else
   let reslt = result + toAttribute(result sub n.result, [inputi])
   let ini = idxNB(myinput, i + 1),
   next(stk, Sstate.te, i + 1, ini, reslt, faili, failresult)
 else if actionState = T' then
  let te = idxNB(packedTable, index.state),
  if inputi = match.te then next(stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
  else next(stk, Fstate.te, i, inputi, result, faili, failresult)
 else
  {match non Terminal}
  let te = idxNB(packedTable, index.state)
  assert action.action.te ∈ [NT, NT*] report "PROBLEM PEG:(state)"
  let newstk = push(stk, frame(Sstate.te, Fstate.te, i, result, faili, failresult)),
  let tmp = [toAttribute(result sub n.result, empty:seq.word)],
  next(newstk, nextState.action.te, i, inputi, tmp, i, tmp),
thisresult.push(stk, frame(state, state, i, result, n.myinput, result)) 