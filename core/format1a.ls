Module format1a

use PEGrules

use UTF8

use bits

use seq.seq.byte

use seq1.byte

use seq.char

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

Function textFormat(myinput:seq.word) UTF8
{OPTION NOINLINE}
let r = parse(myinput, empty:seq.byte, true)
{assert false report trace.r}
UTF8(result.r + tobyte.32)

Function HTMLformat1a(myinput:seq.word) UTF8
{OPTION NOINLINE}
let r = parse(myinput, empty:seq.byte, false)
{assert false report}
UTF8(result.r + tobyte.32)

function addSpace(a:seq.byte) seq.byte
if isempty.a ∨ a sub n.a = tobyte.32 then a else a + tobyte.32

function paragraph(a:seq.byte) seq.byte
{used for text and not html}
a
 + if isempty.a ∨ a sub n.a ≠ tobyte.10 then [tobyte.10] + tobyte.10 else [tobyte.10]

function linebreak(a:seq.byte) seq.byte
{used for text and not html}
if isempty.a then [tobyte.10]
else
 let last = a sub n.a,
 if last = tobyte.32 then a >> 1 + [tobyte.10]
 else if last ≠ tobyte.10 then a + [tobyte.10]
 else a

CN process commands with no space pending

CS process commands with space pending

N no commands with no space pending

S no commands with space pending

NSBA no space before or after

NSB no space before

function endMark word encodeword.[char.254]

function break word "/br" sub 1

function genPEG(
seqElementType:word
, attributeType:seq.byte
, resultType:thisresult
, textOut:boolean
, commonType:boolean
) seq.boolean
{commonName: textOut notablex: wordmap: dq dq sub 1, ec escapeformat, break"/br
"sub 1,"$"sub 1}
[
 "* CN+" = $.0 + X."+"
 , "/-" = $.0 + X."-"
 , "/." = $.0 + X."."
 , "/:" = $.0 + X.":"
 , "/. " = $.0 + X.". "
 , "/: " = $.0 + X.": "
 , "/ dq" = $.0 + X.dq
 , "/(" = $.0 + X."("
 , "/)" = $.0 + X.")"
 , "/{" = $.0 + X."{"
 , "/}" = $.0 + X."}"
 , "/[" = $.0 + X."["
 , "/]" = $.0 + X."]"
 , "/ /!< CN /!>" = $.0 + tobyte.toint.char1."<" + $.1 + tobyte.toint.char1.">" + tobyte.32
 , "/ /sp" = addSpace.$.0
 , "/ /nsp" = $.0
 , "/ break"
 = (if textOut then linebreak.$.0
 else $.0 + toseqbyte(emptyUTF8 + decodeword."<br>" sub 1))
 , "/ /p"
 = (if textOut then paragraph.$.0
 else $.0 + toseqbyte(emptyUTF8 + [char.10, char.10] + decodeword."<p>" sub 1))
 , "/ ec N ec" = $.0 + $.1
 , "/ CS" = $.0 + $.1
 , "+CS," = $.0 + X.","
 , "/ /sp" = addSpace.$.0
 , "/ /!< CN /!>" = $.0 + tobyte.toint.char1."<" + $.1 + tobyte.toint.char1.">"
 , "/ ec N ec" = addSpace.$.0 + $.1
 , "/ !+!-!.!:!. !: ! dq !(!)![!]!{!}! /p ! break ! ec ! /!> ! /!< ! /nsp any"
 = addSpace.$.0 + (if textOut then $.1 else escape&<.$.1)
 , "* N S+" = $.0 + $.1 + X."+"
 , "/ S-" = $.0 + $.1 + X."-"
 , "/ S." = $.0 + $.1 + X."."
 , "/ S:" = $.0 + $.1 + X.":"
 , "/ S. " = $.0 + $.1 + X.". "
 , "/ S: " = $.0 + $.1 + X.": "
 , "/ S dq" = $.0 + $.1 + X.dq
 , "/ S(" = $.0 + $.1 + X."("
 , "/ S)" = $.0 + $.1 + X.")"
 , "/ S{" = $.0 + $.1 + X."{"
 , "/ S}" = $.0 + $.1 + X."}"
 , "/ S[" = $.0 + $.1 + X."["
 , "/ S]" = $.0 + $.1 + X."]"
 , "/ S" = $.0 + $.1
 , "/+" = $.0 + X."+"
 , "/-" = $.0 + X."-"
 , "/." = $.0 + X."."
 , "/:" = $.0 + X.":"
 , "/. " = $.0 + X.". "
 , "/: " = $.0 + X.": "
 , "/ dq" = $.0 + X.dq
 , "/(" = $.0 + X."("
 , "/)" = $.0 + X.")"
 , "/{" = $.0 + X."{"
 , "/}" = $.0 + X."}"
 , "/[" = $.0 + X."["
 , "/]" = $.0 + X."]"
 , "+S," = $.0 + X.","
 , "/ !+!-!.!:!. !: ! dq !(!)![!]!{!}! ec any"
 = addSpace.$.0 + if textOut then $.1 else escape&<.$.1
]

<<<< Below is auto generated code >>>>

/br Non-terminals:CN CS N S /br
Terminals:()+,-.. /!< /!> /nsp /p
/sp:: []any break dq ec{}/br
* CN ←+/-/./:/. /: / dq /(/)/{/}/[/]/ /!< CN /!> / /sp / /nsp / break / /p
/ ec N ec / CS /br
+CS ←, / /sp / /!< CN /!> / ec N ec / !+!-!.!:!. !: ! dq !(!)![!]!{!}! /p
! break ! ec ! /!> ! /!< ! /nsp any /br
* N ← S+/ S-/ S./ S:/ S. / S: / S dq / S(/ S)/ S{/ S}/ S[/ S]/ S /+/-/./:/. /: / dq /(/)/{/}/[/]/br
+S ←, / !+!-!.!:!. !: ! dq !(!)![!]!{!}! ec any

function action(partno:int, R:seq.seq.byte, textOut:boolean) seq.byte
if partno = 2 then R sub n.R + X."+"
else if partno = 3 then R sub n.R + X."-"
else if partno = 4 then R sub n.R + X."."
else if partno = 5 then R sub n.R + X.":"
else if partno = 6 then R sub n.R + X.". "
else if partno = 7 then R sub n.R + X.": "
else if partno = 8 then R sub n.R + X.dq
else if partno = 9 then R sub n.R + X."("
else if partno = 10 then R sub n.R + X.")"
else if partno = 11 then R sub n.R + X."{"
else if partno = 12 then R sub n.R + X."}"
else if partno = 13 then R sub n.R + X."["
else if partno = 14 then R sub n.R + X."]"
else if partno = 15 then
 R sub (n.R - 1)
 + tobyte.toint.char1."<"
 + R sub n.R
 + tobyte.toint.char1.">"
 + tobyte.32
else if partno = 16 then addSpace.R sub n.R
else if partno = 17 then R sub n.R
else if partno = 18 then
 if textOut then linebreak.R sub n.R
 else R sub n.R + toseqbyte(emptyUTF8 + decodeword."<br>" sub 1)
else if partno = 19 then
 if textOut then paragraph.R sub n.R
 else R sub n.R + toseqbyte(emptyUTF8 + [char.10, char.10] + decodeword."<p>" sub 1)
else if partno = 20 then R sub (n.R - 1) + R sub n.R
else if partno = 21 then R sub (n.R - 1) + R sub n.R
else if partno = 22 then R sub n.R + X.","
else if partno = 23 then addSpace.R sub n.R
else if partno = 24 then R sub (n.R - 1) + tobyte.toint.char1."<" + R sub n.R + tobyte.toint.char1.">"
else if partno = 25 then addSpace.R sub (n.R - 1) + R sub n.R
else if partno = 26 then addSpace.R sub (n.R - 1) + if textOut then R sub n.R else escape&<.R sub n.R
else if partno = 27 then R sub (n.R - 1) + R sub n.R + X."+"
else if partno = 28 then R sub (n.R - 1) + R sub n.R + X."-"
else if partno = 29 then R sub (n.R - 1) + R sub n.R + X."."
else if partno = 30 then R sub (n.R - 1) + R sub n.R + X.":"
else if partno = 31 then R sub (n.R - 1) + R sub n.R + X.". "
else if partno = 32 then R sub (n.R - 1) + R sub n.R + X.": "
else if partno = 33 then R sub (n.R - 1) + R sub n.R + X.dq
else if partno = 34 then R sub (n.R - 1) + R sub n.R + X."("
else if partno = 35 then R sub (n.R - 1) + R sub n.R + X.")"
else if partno = 36 then R sub (n.R - 1) + R sub n.R + X."{"
else if partno = 37 then R sub (n.R - 1) + R sub n.R + X."}"
else if partno = 38 then R sub (n.R - 1) + R sub n.R + X."["
else if partno = 39 then R sub (n.R - 1) + R sub n.R + X."]"
else if partno = 40 then R sub (n.R - 1) + R sub n.R
else if partno = 41 then R sub n.R + X."+"
else if partno = 42 then R sub n.R + X."-"
else if partno = 43 then R sub n.R + X."."
else if partno = 44 then R sub n.R + X.":"
else if partno = 45 then R sub n.R + X.". "
else if partno = 46 then R sub n.R + X.": "
else if partno = 47 then R sub n.R + X.dq
else if partno = 48 then R sub n.R + X."("
else if partno = 49 then R sub n.R + X.")"
else if partno = 50 then R sub n.R + X."{"
else if partno = 51 then R sub n.R + X."}"
else if partno = 52 then R sub n.R + X."["
else if partno = 53 then R sub n.R + X."]"
else if partno = 54 then R sub n.R + X.","
else if partno = 55 then addSpace.R sub (n.R - 1) + if textOut then R sub n.R else escape&<.R sub n.R
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
 , {8}tableEntry(T', dq sub 1, Reduce*(8, T'.2), T'.9, "")
 , {9}tableEntry(T', "(" sub 1, Reduce*(9, T'.2), T'.10, "")
 , {10}tableEntry(T', ")" sub 1, Reduce*(10, T'.2), T'.11, "")
 , {11}tableEntry(T', "{" sub 1, Reduce*(11, T'.2), T'.12, "")
 , {12}tableEntry(T', "}" sub 1, Reduce*(12, T'.2), T'.13, "")
 , {13}tableEntry(T', "[" sub 1, Reduce*(13, T'.2), T'.14, "")
 , {14}tableEntry(T', "]" sub 1, Reduce*(14, T'.2), T'.15, "")
 , {15}tableEntry(T', "/!<" sub 1, NT.16, T'.18, "")
 , {16}tableEntry(NT.T'.2, "CN" sub 1, T.17, T'.18, "")
 , {17}tableEntry(T, "/!>" sub 1, Reduce*(15, T'.2), T'.18, "")
 , {18}tableEntry(T', "/sp" sub 1, Reduce*(16, T'.2), T'.19, "")
 , {19}tableEntry(T', "/nsp" sub 1, Reduce*(17, T'.2), T'.20, "")
 , {20}tableEntry(T', "/br" sub 1, Reduce*(18, T'.2), T'.21, "")
 , {21}tableEntry(T', "/p" sub 1, Reduce*(19, T'.2), T'.22, "")
 , {22}tableEntry(T', escapeformat, NT.23, NT.25, "")
 , {23}tableEntry(NT.54, "N" sub 1, T.24, NT.25, "")
 , {24}tableEntry(T, escapeformat, Reduce*(20, T'.2), NT.25, "")
 , {25}tableEntry(NT.T'.26, "CS" sub 1, Reduce*(21, T'.2), Success*, "")
 , {26}tableEntry(T', "," sub 1, Reduce*(22, T'.110), T'.27, "")
 , {27}tableEntry(T', "/sp" sub 1, Reduce*(23, T'.110), T'.28, "")
 , {28}tableEntry(T', "/!<" sub 1, NT.29, T.31, "")
 , {29}tableEntry(NT.T'.2, "CN" sub 1, T.30, T.31, "")
 , {30}tableEntry(T, "/!>" sub 1, Reduce*(24, T'.110), T.31, "")
 , {31}tableEntry(T, escapeformat, NT.32, !T.34, "")
 , {32}tableEntry(NT.54, "N" sub 1, T.33, !T.34, "")
 , {33}tableEntry(T, escapeformat, Reduce*(25, T'.110), !T.34, "")
 , {34}tableEntry(!T, "+" sub 1, Fail, !T.35, "")
 , {35}tableEntry(!T, "-" sub 1, Fail, !T.36, "")
 , {36}tableEntry(!T, "." sub 1, Fail, !T.37, "")
 , {37}tableEntry(!T, ":" sub 1, Fail, !T.38, "")
 , {38}tableEntry(!T, ". " sub 1, Fail, !T.39, "")
 , {39}tableEntry(!T, ": " sub 1, Fail, !T.40, "")
 , {40}tableEntry(!T, dq sub 1, Fail, !T.41, "")
 , {41}tableEntry(!T, "(" sub 1, Fail, !T.42, "")
 , {42}tableEntry(!T, ")" sub 1, Fail, !T.43, "")
 , {43}tableEntry(!T, "[" sub 1, Fail, !T.44, "")
 , {44}tableEntry(!T, "]" sub 1, Fail, !T.45, "")
 , {45}tableEntry(!T, "{" sub 1, Fail, !T.46, "")
 , {46}tableEntry(!T, "}" sub 1, Fail, !T.47, "")
 , {47}tableEntry(!T, "/p" sub 1, Fail, !T.48, "")
 , {48}tableEntry(!T, "/br" sub 1, Fail, !T.49, "")
 , {49}tableEntry(!T, escapeformat, Fail, !T.50, "")
 , {50}tableEntry(!T, "/!>" sub 1, Fail, !T.51, "")
 , {51}tableEntry(!T, "/!<" sub 1, Fail, !T.52, "")
 , {52}tableEntry(!T, "/nsp" sub 1, Fail, MatchAny.53, "")
 , {53}tableEntry(MatchAny, "?" sub 1, Reduce*(26, T'.110), Fail, "")
 , {54}tableEntry(NT.T.94, "S" sub 1, T'.55, T'.81, "")
 , {55}tableEntry(T', "+" sub 1, Reduce*(27, NT.54), T'.57, "")
 , {56}tableEntry(NT.T.94, "S" sub 1, T'.57, T'.81, "")
 , {57}tableEntry(T', "-" sub 1, Reduce*(28, NT.54), T'.59, "")
 , {58}tableEntry(NT.T.94, "S" sub 1, T'.59, T'.81, "")
 , {59}tableEntry(T', "." sub 1, Reduce*(29, NT.54), T'.61, "")
 , {60}tableEntry(NT.T.94, "S" sub 1, T'.61, T'.81, "")
 , {61}tableEntry(T', ":" sub 1, Reduce*(30, NT.54), T'.63, "")
 , {62}tableEntry(NT.T.94, "S" sub 1, T'.63, T'.81, "")
 , {63}tableEntry(T', ". " sub 1, Reduce*(31, NT.54), T'.65, "")
 , {64}tableEntry(NT.T.94, "S" sub 1, T'.65, T'.81, "")
 , {65}tableEntry(T', ": " sub 1, Reduce*(32, NT.54), T'.67, "")
 , {66}tableEntry(NT.T.94, "S" sub 1, T'.67, T'.81, "")
 , {67}tableEntry(T', dq sub 1, Reduce*(33, NT.54), T'.69, "")
 , {68}tableEntry(NT.T.94, "S" sub 1, T'.69, T'.81, "")
 , {69}tableEntry(T', "(" sub 1, Reduce*(34, NT.54), T'.71, "")
 , {70}tableEntry(NT.T.94, "S" sub 1, T'.71, T'.81, "")
 , {71}tableEntry(T', ")" sub 1, Reduce*(35, NT.54), T'.73, "")
 , {72}tableEntry(NT.T.94, "S" sub 1, T'.73, T'.81, "")
 , {73}tableEntry(T', "{" sub 1, Reduce*(36, NT.54), T'.75, "")
 , {74}tableEntry(NT.T.94, "S" sub 1, T'.75, T'.81, "")
 , {75}tableEntry(T', "}" sub 1, Reduce*(37, NT.54), T'.77, "")
 , {76}tableEntry(NT.T.94, "S" sub 1, T'.77, T'.81, "")
 , {77}tableEntry(T', "[" sub 1, Reduce*(38, NT.54), T.79, "")
 , {78}tableEntry(NT.T.94, "S" sub 1, T.79, T'.81, "")
 , {79}tableEntry(T, "]" sub 1, Reduce*(39, NT.54), NT.80, "")
 , {80}tableEntry(NT.T.94, "S" sub 1, Reduce*(40, NT.54), T'.81, "")
 , {81}tableEntry(T', "+" sub 1, Reduce*(41, NT.54), T'.82, "")
 , {82}tableEntry(T', "-" sub 1, Reduce*(42, NT.54), T'.83, "")
 , {83}tableEntry(T', "." sub 1, Reduce*(43, NT.54), T'.84, "")
 , {84}tableEntry(T', ":" sub 1, Reduce*(44, NT.54), T'.85, "")
 , {85}tableEntry(T', ". " sub 1, Reduce*(45, NT.54), T'.86, "")
 , {86}tableEntry(T', ": " sub 1, Reduce*(46, NT.54), T'.87, "")
 , {87}tableEntry(T', dq sub 1, Reduce*(47, NT.54), T'.88, "")
 , {88}tableEntry(T', "(" sub 1, Reduce*(48, NT.54), T'.89, "")
 , {89}tableEntry(T', ")" sub 1, Reduce*(49, NT.54), T'.90, "")
 , {90}tableEntry(T', "{" sub 1, Reduce*(50, NT.54), T'.91, "")
 , {91}tableEntry(T', "}" sub 1, Reduce*(51, NT.54), T'.92, "")
 , {92}tableEntry(T', "[" sub 1, Reduce*(52, NT.54), T.93, "")
 , {93}tableEntry(T, "]" sub 1, Reduce*(53, NT.54), Success*, "")
 , {94}tableEntry(T, "," sub 1, Reduce*(54, T.138), !T.95, "")
 , {95}tableEntry(!T, "+" sub 1, Fail, !T.96, "")
 , {96}tableEntry(!T, "-" sub 1, Fail, !T.97, "")
 , {97}tableEntry(!T, "." sub 1, Fail, !T.98, "")
 , {98}tableEntry(!T, ":" sub 1, Fail, !T.99, "")
 , {99}tableEntry(!T, ". " sub 1, Fail, !T.100, "")
 , {100}tableEntry(!T, ": " sub 1, Fail, !T.101, "")
 , {101}tableEntry(!T, dq sub 1, Fail, !T.102, "")
 , {102}tableEntry(!T, "(" sub 1, Fail, !T.103, "")
 , {103}tableEntry(!T, ")" sub 1, Fail, !T.104, "")
 , {104}tableEntry(!T, "[" sub 1, Fail, !T.105, "")
 , {105}tableEntry(!T, "]" sub 1, Fail, !T.106, "")
 , {106}tableEntry(!T, "{" sub 1, Fail, !T.107, "")
 , {107}tableEntry(!T, "}" sub 1, Fail, !T.108, "")
 , {108}tableEntry(!T, escapeformat, Fail, MatchAny.109, "")
 , {109}tableEntry(MatchAny, "?" sub 1, Reduce*(55, T.138), Fail, "")
 , {110}tableEntry(T', "," sub 1, Reduce*(22, T'.110), T'.111, "")
 , {111}tableEntry(T', "/sp" sub 1, Reduce*(23, T'.110), T'.112, "")
 , {112}tableEntry(T', "/!<" sub 1, NT.113, T.115, "")
 , {113}tableEntry(NT.T'.2, "CN" sub 1, T.114, T.115, "")
 , {114}tableEntry(T, "/!>" sub 1, Reduce*(24, T'.110), T.115, "")
 , {115}tableEntry(T, escapeformat, NT.116, !T.118, "")
 , {116}tableEntry(NT.54, "N" sub 1, T.117, !T.118, "")
 , {117}tableEntry(T, escapeformat, Reduce*(25, T'.110), !T.118, "")
 , {118}tableEntry(!T, "+" sub 1, Success*, !T.119, "")
 , {119}tableEntry(!T, "-" sub 1, Success*, !T.120, "")
 , {120}tableEntry(!T, "." sub 1, Success*, !T.121, "")
 , {121}tableEntry(!T, ":" sub 1, Success*, !T.122, "")
 , {122}tableEntry(!T, ". " sub 1, Success*, !T.123, "")
 , {123}tableEntry(!T, ": " sub 1, Success*, !T.124, "")
 , {124}tableEntry(!T, dq sub 1, Success*, !T.125, "")
 , {125}tableEntry(!T, "(" sub 1, Success*, !T.126, "")
 , {126}tableEntry(!T, ")" sub 1, Success*, !T.127, "")
 , {127}tableEntry(!T, "[" sub 1, Success*, !T.128, "")
 , {128}tableEntry(!T, "]" sub 1, Success*, !T.129, "")
 , {129}tableEntry(!T, "{" sub 1, Success*, !T.130, "")
 , {130}tableEntry(!T, "}" sub 1, Success*, !T.131, "")
 , {131}tableEntry(!T, "/p" sub 1, Success*, !T.132, "")
 , {132}tableEntry(!T, "/br" sub 1, Success*, !T.133, "")
 , {133}tableEntry(!T, escapeformat, Success*, !T.134, "")
 , {134}tableEntry(!T, "/!>" sub 1, Success*, !T.135, "")
 , {135}tableEntry(!T, "/!<" sub 1, Success*, !T.136, "")
 , {136}tableEntry(!T, "/nsp" sub 1, Success*, MatchAny.137, "")
 , {137}tableEntry(MatchAny, "?" sub 1, Reduce*(26, T'.110), Success*, "")
 , {138}tableEntry(T, "," sub 1, Reduce*(54, T.138), !T.139, "")
 , {139}tableEntry(!T, "+" sub 1, Success*, !T.140, "")
 , {140}tableEntry(!T, "-" sub 1, Success*, !T.141, "")
 , {141}tableEntry(!T, "." sub 1, Success*, !T.142, "")
 , {142}tableEntry(!T, ":" sub 1, Success*, !T.143, "")
 , {143}tableEntry(!T, ". " sub 1, Success*, !T.144, "")
 , {144}tableEntry(!T, ": " sub 1, Success*, !T.145, "")
 , {145}tableEntry(!T, dq sub 1, Success*, !T.146, "")
 , {146}tableEntry(!T, "(" sub 1, Success*, !T.147, "")
 , {147}tableEntry(!T, ")" sub 1, Success*, !T.148, "")
 , {148}tableEntry(!T, "[" sub 1, Success*, !T.149, "")
 , {149}tableEntry(!T, "]" sub 1, Success*, !T.150, "")
 , {150}tableEntry(!T, "{" sub 1, Success*, !T.151, "")
 , {151}tableEntry(!T, "}" sub 1, Success*, !T.152, "")
 , {152}tableEntry(!T, escapeformat, Success*, MatchAny.153, "")
 , {153}tableEntry(MatchAny, "?" sub 1, Reduce*(55, T.138), Success*, "")
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

Function result(a:thisresult) seq.byte last.result.top.stk.a

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
  if inputi ≠ match.te then {fail}next(stk, Fstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
  else next(stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
 else if actionState = !T then
  let te = idxNB(packedTable, index.state),
  if inputi = match.te then {fail}next(stk, Sstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
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