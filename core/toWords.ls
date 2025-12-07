Module toWords

use UTF8

use bits

use seq.byte

use seq.int

use standard

use seq.word

use seq.seq.word

use seq.tblrec

use seq1.seq.word

Function towords(a:UTF8) seq.word
{assumes no paragraph breaks in a}
let b = breakparagraph.toseqbyte.a,
if isempty.b then empty:seq.word else b sub 1

Function breakparagraph(bytes:seq.byte) seq.seq.word
{breaks file into seq of paragraphs. Paragraphs are delimited by one or blank lines.}
test(bytes, tableText)

Function fromHTML(bytes:seq.byte) seq.seq.word
{input is broken into paragraphs when each paragraph is either an HTML element or is text. Paragraphs of text end with a double quote.}
test(bytes, tableHTML)

type tblrec is kind:int, chr:char

function handleCharRef(chars:seq.char, ch:char) seq.char
if ch = char1.";" then
 let list = decodeword."<&" sub 1
 for acc = empty:seq.char, idx = 1, e ∈ [decodeword."&lt" sub 1, decodeword."&amp" sub 1]
 do
  if subseq(chars, n.chars - n.e + 1, n.chars) = e then next(subseq(chars, n.e + 1, n.e) + list sub idx, idx + 1)
  else next(acc, idx + 1),
 if isempty.acc then chars + ch else acc
else chars + ch

function test(bytes:seq.byte, classify:seq.tblrec) seq.seq.word
let period/colon = 1
{period or colon is pending waiting for next character}
for
 tag = false
 , state0 = 0
 , paragraph0 = empty:seq.seq.word
 , chars0 = empty:seq.char
 , gather = bits.0
 , expect = 0
 , words0 = ""
 , b ∈ bytes + tobyte.32
do
 let tabrec = classify sub (toint.b + 1)
 let bits = tobits.toint.b
 let kind = kind.tabrec
 let ch = chr.tabrec,
 for state = state0, paragraph = paragraph0, words = words0, chars = chars0, e ∈ [1]
 do
  {???? make sure this for does not use loop in final code.}
  if state = 0 then next(state, paragraph, words, chars)
  else if state = period/colon then
   let newwords =
    encodeword(chars0 + (if ch = {space}char.32 then [char.32] else empty:seq.char)),
   next(0, paragraph, words + newwords, empty:seq.char)
  else if state = 2 then
   {found first LF and looking for second LF}
   let newstate = if kind = Space then if ch = {LF}char.10 then 3 else 2 else 0,
   next(newstate, paragraph, words, chars)
  else
   assert state = 3 report "State problem",
   if kind = Space then {remain in state 3}next(state, paragraph, words, chars)
   else
    {finish paragraph}
    next(0, if isempty.words then paragraph else paragraph + [words], "", chars),
 if kind = Char&< then
  {starting a tag}
  let newwords = if n.chars = 0 then words else words + encodeword.chars,
  if ch = char1.">" then
   {assert ch ∈(decodeword."<!doctypehml"sub 1+char.32)report"ch:(tag)"+encodeword.[ch]}
   if tag then
    let newpara =
     paragraph
     + if subseq(chars, 1, 2) = decodeword."</" sub 1 then [words] + [encodeword(chars + ch)]
     else [words] + [[encodeword.chars] + ">"],
    next(false, state, newpara, empty:seq.char, bits.0, 0, "")
   else if isempty.words ∨ char1.words ≠ char1."<" then
    {???? A more general solution is needed to determine whether a '>' marks the end of an element tag. Does not handle the case where the first word of text is a less than.}
    next(false, 0, paragraph, chars + ch, bits.0, 0, words)
   else
    let newpara = paragraph + [words + [encodeword.chars] + ">"],
    next(false, 0, newpara, empty:seq.char, bits.0, 0, "")
  else if ch = char1."<" ∧ not.isempty.newwords ∧ last.newwords ∉ ">" then next(true, 0, paragraph + [newwords + dq], [ch], bits.0, 0, "")
  else next(true, 0, paragraph, [ch], bits.0, 0, newwords)
 else if kind = Space then
  if tag then
   let newpara = paragraph + if isempty.words0 then empty:seq.seq.word else [words0],
   next(false, state, newpara, empty:seq.char, bits.0, 0, [encodeword.chars])
  else
   let newwords = if n.chars = 0 then words else words + encodeword.chars
   let newstate = if ch = {LF}char.10 ∧ state = 0 then 2 else state,
   next(tag, newstate, paragraph, empty:seq.char, bits.0, 0, newwords)
 else if kind = 0 then
  if tag then next(ch ≠ char1.";", 0, paragraph, handleCharRef(chars, ch), bits.0, 0, words)
  else next(tag, 0, paragraph, chars + ch, bits.0, 0, words)
 else if kind = ThreeByte then next(tag, 0, paragraph, chars, 0xF ∧ bits, 2, words)
 else if kind = TwoByte then next(tag, 0, paragraph, chars, 0x1F ∧ bits, 1, words)
 else if kind = FourByte then next(tag, 0, paragraph, chars, 0x7 ∧ bits, 3, words)
 else if kind = More then
  let newbits = gather << 6 ∨ 0x3F ∧ bits,
  if expect = 1 then next(tag, 0, paragraph, chars + char.toint.newbits, bits.0, 0, words)
  else
   assert expect > 0 report "error",
   next(tag, 0, paragraph, chars, newbits, expect - 1, words)
 else if kind = StandAlone then
  let newwords = if n.chars = 0 then words else words + encodeword.chars,
  next(tag, 0, paragraph, empty:seq.char, bits.0, 0, newwords + encodeword.[ch])
 else if kind = Period then
  let newwords = if n.chars = 0 then words else words + encodeword.chars,
  next(tag, period/colon, paragraph, [ch], bits.0, 0, newwords)
 else
  assert false report "kind:(kind)",
  next(tag, 0, paragraph, chars, bits.0, 0, words),
if isempty.words0 then paragraph0
else
 let html = kind.classify sub (toint.char1."<" + 1) = Char&<,
 paragraph0 + [if html then words0 + dq else words0]

function Invalid int 1

function More int 2

function TwoByte int 3

function ThreeByte int 4

function FourByte int 5

function StandAlone int 6

function Space int 7

function Period int 8

function Char&< int 9

function tableHTML seq.tblrec
{auto generated}
[
 {00}tblrec(0, char.0)
 , {01}tblrec(0, char.1)
 , {02}tblrec(0, char.2)
 , {03}tblrec(0, char.3)
 , {04}tblrec(0, char.4)
 , {05}tblrec(0, char.5)
 , {06}tblrec(0, char.6)
 , {07}tblrec(0, char.7)
 , {08}tblrec(0, char.8)
 , {09}tblrec(0, char.9)
 , {0A}tblrec(Space, char.10)
 , {0B}tblrec(0, char.11)
 , {0C}tblrec(0, char.12)
 , {0D}tblrec(Space, char.13)
 , {0E}tblrec(0, char.14)
 , {0F}tblrec(0, char.15)
 , {10}tblrec(0, char.16)
 , {11}tblrec(0, char.17)
 , {12}tblrec(0, char.18)
 , {13}tblrec(0, char.19)
 , {14}tblrec(0, char.20)
 , {15}tblrec(0, char.21)
 , {16}tblrec(0, char.22)
 , {17}tblrec(0, char.23)
 , {18}tblrec(0, char.24)
 , {19}tblrec(0, char.25)
 , {1A}tblrec(0, char.26)
 , {1B}tblrec(0, char.27)
 , {1C}tblrec(0, char.28)
 , {1D}tblrec(0, char.29)
 , {1E}tblrec(0, char.30)
 , {1F}tblrec(0, char.31)
 , {20}tblrec(Space, char.32)
 , {21}tblrec(0, char1."!")
 , {22}tblrec(StandAlone, char1.dq)
 , {23}tblrec(0, char1."#")
 , {24}tblrec(0, char1."$")
 , {25}tblrec(0, char1."%")
 , {26}tblrec(Char&<, char1."&")
 , {27}tblrec(0, char1."'")
 , {28}tblrec(StandAlone, char1."(")
 , {29}tblrec(StandAlone, char1.")")
 , {2A}tblrec(0, char1."*")
 , {2B}tblrec(StandAlone, char1."+")
 , {2C}tblrec(StandAlone, char1.",")
 , {2D}tblrec(StandAlone, char1."-")
 , {2E}tblrec(Period, char1.".")
 , {2F}tblrec(0, char1."/")
 , {30}tblrec(0, char1."0")
 , {31}tblrec(0, char1."1")
 , {32}tblrec(0, char1."2")
 , {33}tblrec(0, char1."3")
 , {34}tblrec(0, char1."4")
 , {35}tblrec(0, char1."5")
 , {36}tblrec(0, char1."6")
 , {37}tblrec(0, char1."7")
 , {38}tblrec(0, char1."8")
 , {39}tblrec(0, char1."9")
 , {3A}tblrec(Period, char1.":")
 , {3B}tblrec(0, char1.";")
 , {3C}tblrec(Char&<, char1."<")
 , {3D}tblrec(StandAlone, char1."=")
 , {3E}tblrec(Char&<, char1.">")
 , {3F}tblrec(0, char1."?")
 , {40}tblrec(0, char1."@")
 , {41}tblrec(0, char1."A")
 , {42}tblrec(0, char1."B")
 , {43}tblrec(0, char1."C")
 , {44}tblrec(0, char1."D")
 , {45}tblrec(0, char1."E")
 , {46}tblrec(0, char1."F")
 , {47}tblrec(0, char1."G")
 , {48}tblrec(0, char1."H")
 , {49}tblrec(0, char1."I")
 , {4A}tblrec(0, char1."J")
 , {4B}tblrec(0, char1."K")
 , {4C}tblrec(0, char1."L")
 , {4D}tblrec(0, char1."M")
 , {4E}tblrec(0, char1."N")
 , {4F}tblrec(0, char1."O")
 , {50}tblrec(0, char1."P")
 , {51}tblrec(0, char1."Q")
 , {52}tblrec(0, char1."R")
 , {53}tblrec(0, char1."S")
 , {54}tblrec(0, char1."T")
 , {55}tblrec(0, char1."U")
 , {56}tblrec(0, char1."V")
 , {57}tblrec(0, char1."W")
 , {58}tblrec(0, char1."X")
 , {59}tblrec(0, char1."Y")
 , {5A}tblrec(0, char1."Z")
 , {5B}tblrec(StandAlone, char1."[")
 , {5C}tblrec(0, char1."\")
 , {5D}tblrec(StandAlone, char1."]")
 , {5E}tblrec(0, char1."^")
 , {5F}tblrec(0, char1."_")
 , {60}tblrec(0, char1."`")
 , {61}tblrec(0, char1."a")
 , {62}tblrec(0, char1."b")
 , {63}tblrec(0, char1."c")
 , {64}tblrec(0, char1."d")
 , {65}tblrec(0, char1."e")
 , {66}tblrec(0, char1."f")
 , {67}tblrec(0, char1."g")
 , {68}tblrec(0, char1."h")
 , {69}tblrec(0, char1."i")
 , {6A}tblrec(0, char1."j")
 , {6B}tblrec(0, char1."k")
 , {6C}tblrec(0, char1."l")
 , {6D}tblrec(0, char1."m")
 , {6E}tblrec(0, char1."n")
 , {6F}tblrec(0, char1."o")
 , {70}tblrec(0, char1."p")
 , {71}tblrec(0, char1."q")
 , {72}tblrec(0, char1."r")
 , {73}tblrec(0, char1."s")
 , {74}tblrec(0, char1."t")
 , {75}tblrec(0, char1."u")
 , {76}tblrec(0, char1."v")
 , {77}tblrec(0, char1."w")
 , {78}tblrec(0, char1."x")
 , {79}tblrec(0, char1."y")
 , {7A}tblrec(0, char1."z")
 , {7B}tblrec(StandAlone, char1."{")
 , {7C}tblrec(0, char1."|")
 , {7D}tblrec(StandAlone, char1."}")
 , {7E}tblrec(0, char1."~")
 , {7F}tblrec(0, char1."")
 , {80}tblrec(More, char.128)
 , {81}tblrec(More, char.129)
 , {82}tblrec(More, char.130)
 , {83}tblrec(More, char.131)
 , {84}tblrec(More, char.132)
 , {85}tblrec(More, char.133)
 , {86}tblrec(More, char.134)
 , {87}tblrec(More, char.135)
 , {88}tblrec(More, char.136)
 , {89}tblrec(More, char.137)
 , {8A}tblrec(More, char.138)
 , {8B}tblrec(More, char.139)
 , {8C}tblrec(More, char.140)
 , {8D}tblrec(More, char.141)
 , {8E}tblrec(More, char.142)
 , {8F}tblrec(More, char.143)
 , {90}tblrec(More, char.144)
 , {91}tblrec(More, char.145)
 , {92}tblrec(More, char.146)
 , {93}tblrec(More, char.147)
 , {94}tblrec(More, char.148)
 , {95}tblrec(More, char.149)
 , {96}tblrec(More, char.150)
 , {97}tblrec(More, char.151)
 , {98}tblrec(More, char.152)
 , {99}tblrec(More, char.153)
 , {9A}tblrec(More, char.154)
 , {9B}tblrec(More, char.155)
 , {9C}tblrec(More, char.156)
 , {9D}tblrec(More, char.157)
 , {9E}tblrec(More, char.158)
 , {9F}tblrec(More, char.159)
 , {A0}tblrec(More, char.160)
 , {A1}tblrec(More, char.161)
 , {A2}tblrec(More, char.162)
 , {A3}tblrec(More, char.163)
 , {A4}tblrec(More, char.164)
 , {A5}tblrec(More, char.165)
 , {A6}tblrec(More, char.166)
 , {A7}tblrec(More, char.167)
 , {A8}tblrec(More, char.168)
 , {A9}tblrec(More, char.169)
 , {AA}tblrec(More, char.170)
 , {AB}tblrec(More, char.171)
 , {AC}tblrec(More, char.172)
 , {AD}tblrec(More, char.173)
 , {AE}tblrec(More, char.174)
 , {AF}tblrec(More, char.175)
 , {B0}tblrec(More, char.176)
 , {B1}tblrec(More, char.177)
 , {B2}tblrec(More, char.178)
 , {B3}tblrec(More, char.179)
 , {B4}tblrec(More, char.180)
 , {B5}tblrec(More, char.181)
 , {B6}tblrec(More, char.182)
 , {B7}tblrec(More, char.183)
 , {B8}tblrec(More, char.184)
 , {B9}tblrec(More, char.185)
 , {BA}tblrec(More, char.186)
 , {BB}tblrec(More, char.187)
 , {BC}tblrec(More, char.188)
 , {BD}tblrec(More, char.189)
 , {BE}tblrec(More, char.190)
 , {BF}tblrec(More, char.191)
 , {C0}tblrec(TwoByte, char.192)
 , {C1}tblrec(TwoByte, char.193)
 , {C2}tblrec(TwoByte, char.194)
 , {C3}tblrec(TwoByte, char.195)
 , {C4}tblrec(TwoByte, char.196)
 , {C5}tblrec(TwoByte, char.197)
 , {C6}tblrec(TwoByte, char.198)
 , {C7}tblrec(TwoByte, char.199)
 , {C8}tblrec(TwoByte, char.200)
 , {C9}tblrec(TwoByte, char.201)
 , {CA}tblrec(TwoByte, char.202)
 , {CB}tblrec(TwoByte, char.203)
 , {CC}tblrec(TwoByte, char.204)
 , {CD}tblrec(TwoByte, char.205)
 , {CE}tblrec(TwoByte, char.206)
 , {CF}tblrec(TwoByte, char.207)
 , {D0}tblrec(TwoByte, char.208)
 , {D1}tblrec(TwoByte, char.209)
 , {D2}tblrec(TwoByte, char.210)
 , {D3}tblrec(TwoByte, char.211)
 , {D4}tblrec(TwoByte, char.212)
 , {D5}tblrec(TwoByte, char.213)
 , {D6}tblrec(TwoByte, char.214)
 , {D7}tblrec(TwoByte, char.215)
 , {D8}tblrec(TwoByte, char.216)
 , {D9}tblrec(TwoByte, char.217)
 , {DA}tblrec(TwoByte, char.218)
 , {DB}tblrec(TwoByte, char.219)
 , {DC}tblrec(TwoByte, char.220)
 , {DD}tblrec(TwoByte, char.221)
 , {DE}tblrec(TwoByte, char.222)
 , {DF}tblrec(TwoByte, char.223)
 , {E0}tblrec(ThreeByte, char.224)
 , {E1}tblrec(ThreeByte, char.225)
 , {E2}tblrec(ThreeByte, char.226)
 , {E3}tblrec(ThreeByte, char.227)
 , {E4}tblrec(ThreeByte, char.228)
 , {E5}tblrec(ThreeByte, char.229)
 , {E6}tblrec(ThreeByte, char.230)
 , {E7}tblrec(ThreeByte, char.231)
 , {E8}tblrec(ThreeByte, char.232)
 , {E9}tblrec(ThreeByte, char.233)
 , {EA}tblrec(ThreeByte, char.234)
 , {EB}tblrec(ThreeByte, char.235)
 , {EC}tblrec(ThreeByte, char.236)
 , {ED}tblrec(ThreeByte, char.237)
 , {EE}tblrec(ThreeByte, char.238)
 , {EF}tblrec(ThreeByte, char.239)
 , {F0}tblrec(FourByte, char.240)
 , {F1}tblrec(FourByte, char.241)
 , {F2}tblrec(FourByte, char.242)
 , {F3}tblrec(FourByte, char.243)
 , {F4}tblrec(FourByte, char.244)
 , {F5}tblrec(FourByte, char.245)
 , {F6}tblrec(FourByte, char.246)
 , {F7}tblrec(FourByte, char.247)
 , {F8}tblrec(Invalid, char.248)
 , {F9}tblrec(Invalid, char.249)
 , {FA}tblrec(Invalid, char.250)
 , {FB}tblrec(Invalid, char.251)
 , {FC}tblrec(Invalid, char.252)
 , {FD}tblrec(Invalid, char.253)
 , {FE}tblrec(Invalid, char.254)
 , {FF}tblrec(Invalid, char.255)
]

function tableText seq.tblrec
{auto generated}
[
 {00}tblrec(0, char.0)
 , {01}tblrec(0, char.1)
 , {02}tblrec(0, char.2)
 , {03}tblrec(0, char.3)
 , {04}tblrec(0, char.4)
 , {05}tblrec(0, char.5)
 , {06}tblrec(0, char.6)
 , {07}tblrec(0, char.7)
 , {08}tblrec(0, char.8)
 , {09}tblrec(0, char.9)
 , {0A}tblrec(Space, char.10)
 , {0B}tblrec(0, char.11)
 , {0C}tblrec(0, char.12)
 , {0D}tblrec(Space, char.13)
 , {0E}tblrec(0, char.14)
 , {0F}tblrec(0, char.15)
 , {10}tblrec(0, char.16)
 , {11}tblrec(0, char.17)
 , {12}tblrec(0, char.18)
 , {13}tblrec(0, char.19)
 , {14}tblrec(0, char.20)
 , {15}tblrec(0, char.21)
 , {16}tblrec(0, char.22)
 , {17}tblrec(0, char.23)
 , {18}tblrec(0, char.24)
 , {19}tblrec(0, char.25)
 , {1A}tblrec(0, char.26)
 , {1B}tblrec(0, char.27)
 , {1C}tblrec(0, char.28)
 , {1D}tblrec(0, char.29)
 , {1E}tblrec(0, char.30)
 , {1F}tblrec(0, char.31)
 , {20}tblrec(Space, char.32)
 , {21}tblrec(0, char1."!")
 , {22}tblrec(StandAlone, char1.dq)
 , {23}tblrec(0, char1."#")
 , {24}tblrec(0, char1."$")
 , {25}tblrec(0, char1."%")
 , {26}tblrec(0, char1."&")
 , {27}tblrec(0, char1."'")
 , {28}tblrec(StandAlone, char1."(")
 , {29}tblrec(StandAlone, char1.")")
 , {2A}tblrec(0, char1."*")
 , {2B}tblrec(StandAlone, char1."+")
 , {2C}tblrec(StandAlone, char1.",")
 , {2D}tblrec(StandAlone, char1."-")
 , {2E}tblrec(Period, char1.".")
 , {2F}tblrec(0, char1."/")
 , {30}tblrec(0, char1."0")
 , {31}tblrec(0, char1."1")
 , {32}tblrec(0, char1."2")
 , {33}tblrec(0, char1."3")
 , {34}tblrec(0, char1."4")
 , {35}tblrec(0, char1."5")
 , {36}tblrec(0, char1."6")
 , {37}tblrec(0, char1."7")
 , {38}tblrec(0, char1."8")
 , {39}tblrec(0, char1."9")
 , {3A}tblrec(Period, char1.":")
 , {3B}tblrec(0, char1.";")
 , {3C}tblrec(0, char1."<")
 , {3D}tblrec(StandAlone, char1."=")
 , {3E}tblrec(0, char1.">")
 , {3F}tblrec(0, char1."?")
 , {40}tblrec(0, char1."@")
 , {41}tblrec(0, char1."A")
 , {42}tblrec(0, char1."B")
 , {43}tblrec(0, char1."C")
 , {44}tblrec(0, char1."D")
 , {45}tblrec(0, char1."E")
 , {46}tblrec(0, char1."F")
 , {47}tblrec(0, char1."G")
 , {48}tblrec(0, char1."H")
 , {49}tblrec(0, char1."I")
 , {4A}tblrec(0, char1."J")
 , {4B}tblrec(0, char1."K")
 , {4C}tblrec(0, char1."L")
 , {4D}tblrec(0, char1."M")
 , {4E}tblrec(0, char1."N")
 , {4F}tblrec(0, char1."O")
 , {50}tblrec(0, char1."P")
 , {51}tblrec(0, char1."Q")
 , {52}tblrec(0, char1."R")
 , {53}tblrec(0, char1."S")
 , {54}tblrec(0, char1."T")
 , {55}tblrec(0, char1."U")
 , {56}tblrec(0, char1."V")
 , {57}tblrec(0, char1."W")
 , {58}tblrec(0, char1."X")
 , {59}tblrec(0, char1."Y")
 , {5A}tblrec(0, char1."Z")
 , {5B}tblrec(StandAlone, char1."[")
 , {5C}tblrec(0, char1."\")
 , {5D}tblrec(StandAlone, char1."]")
 , {5E}tblrec(0, char1."^")
 , {5F}tblrec(0, char1."_")
 , {60}tblrec(0, char1."`")
 , {61}tblrec(0, char1."a")
 , {62}tblrec(0, char1."b")
 , {63}tblrec(0, char1."c")
 , {64}tblrec(0, char1."d")
 , {65}tblrec(0, char1."e")
 , {66}tblrec(0, char1."f")
 , {67}tblrec(0, char1."g")
 , {68}tblrec(0, char1."h")
 , {69}tblrec(0, char1."i")
 , {6A}tblrec(0, char1."j")
 , {6B}tblrec(0, char1."k")
 , {6C}tblrec(0, char1."l")
 , {6D}tblrec(0, char1."m")
 , {6E}tblrec(0, char1."n")
 , {6F}tblrec(0, char1."o")
 , {70}tblrec(0, char1."p")
 , {71}tblrec(0, char1."q")
 , {72}tblrec(0, char1."r")
 , {73}tblrec(0, char1."s")
 , {74}tblrec(0, char1."t")
 , {75}tblrec(0, char1."u")
 , {76}tblrec(0, char1."v")
 , {77}tblrec(0, char1."w")
 , {78}tblrec(0, char1."x")
 , {79}tblrec(0, char1."y")
 , {7A}tblrec(0, char1."z")
 , {7B}tblrec(StandAlone, char1."{")
 , {7C}tblrec(0, char1."|")
 , {7D}tblrec(StandAlone, char1."}")
 , {7E}tblrec(0, char1."~")
 , {7F}tblrec(0, char1."")
 , {80}tblrec(More, char.128)
 , {81}tblrec(More, char.129)
 , {82}tblrec(More, char.130)
 , {83}tblrec(More, char.131)
 , {84}tblrec(More, char.132)
 , {85}tblrec(More, char.133)
 , {86}tblrec(More, char.134)
 , {87}tblrec(More, char.135)
 , {88}tblrec(More, char.136)
 , {89}tblrec(More, char.137)
 , {8A}tblrec(More, char.138)
 , {8B}tblrec(More, char.139)
 , {8C}tblrec(More, char.140)
 , {8D}tblrec(More, char.141)
 , {8E}tblrec(More, char.142)
 , {8F}tblrec(More, char.143)
 , {90}tblrec(More, char.144)
 , {91}tblrec(More, char.145)
 , {92}tblrec(More, char.146)
 , {93}tblrec(More, char.147)
 , {94}tblrec(More, char.148)
 , {95}tblrec(More, char.149)
 , {96}tblrec(More, char.150)
 , {97}tblrec(More, char.151)
 , {98}tblrec(More, char.152)
 , {99}tblrec(More, char.153)
 , {9A}tblrec(More, char.154)
 , {9B}tblrec(More, char.155)
 , {9C}tblrec(More, char.156)
 , {9D}tblrec(More, char.157)
 , {9E}tblrec(More, char.158)
 , {9F}tblrec(More, char.159)
 , {A0}tblrec(More, char.160)
 , {A1}tblrec(More, char.161)
 , {A2}tblrec(More, char.162)
 , {A3}tblrec(More, char.163)
 , {A4}tblrec(More, char.164)
 , {A5}tblrec(More, char.165)
 , {A6}tblrec(More, char.166)
 , {A7}tblrec(More, char.167)
 , {A8}tblrec(More, char.168)
 , {A9}tblrec(More, char.169)
 , {AA}tblrec(More, char.170)
 , {AB}tblrec(More, char.171)
 , {AC}tblrec(More, char.172)
 , {AD}tblrec(More, char.173)
 , {AE}tblrec(More, char.174)
 , {AF}tblrec(More, char.175)
 , {B0}tblrec(More, char.176)
 , {B1}tblrec(More, char.177)
 , {B2}tblrec(More, char.178)
 , {B3}tblrec(More, char.179)
 , {B4}tblrec(More, char.180)
 , {B5}tblrec(More, char.181)
 , {B6}tblrec(More, char.182)
 , {B7}tblrec(More, char.183)
 , {B8}tblrec(More, char.184)
 , {B9}tblrec(More, char.185)
 , {BA}tblrec(More, char.186)
 , {BB}tblrec(More, char.187)
 , {BC}tblrec(More, char.188)
 , {BD}tblrec(More, char.189)
 , {BE}tblrec(More, char.190)
 , {BF}tblrec(More, char.191)
 , {C0}tblrec(TwoByte, char.192)
 , {C1}tblrec(TwoByte, char.193)
 , {C2}tblrec(TwoByte, char.194)
 , {C3}tblrec(TwoByte, char.195)
 , {C4}tblrec(TwoByte, char.196)
 , {C5}tblrec(TwoByte, char.197)
 , {C6}tblrec(TwoByte, char.198)
 , {C7}tblrec(TwoByte, char.199)
 , {C8}tblrec(TwoByte, char.200)
 , {C9}tblrec(TwoByte, char.201)
 , {CA}tblrec(TwoByte, char.202)
 , {CB}tblrec(TwoByte, char.203)
 , {CC}tblrec(TwoByte, char.204)
 , {CD}tblrec(TwoByte, char.205)
 , {CE}tblrec(TwoByte, char.206)
 , {CF}tblrec(TwoByte, char.207)
 , {D0}tblrec(TwoByte, char.208)
 , {D1}tblrec(TwoByte, char.209)
 , {D2}tblrec(TwoByte, char.210)
 , {D3}tblrec(TwoByte, char.211)
 , {D4}tblrec(TwoByte, char.212)
 , {D5}tblrec(TwoByte, char.213)
 , {D6}tblrec(TwoByte, char.214)
 , {D7}tblrec(TwoByte, char.215)
 , {D8}tblrec(TwoByte, char.216)
 , {D9}tblrec(TwoByte, char.217)
 , {DA}tblrec(TwoByte, char.218)
 , {DB}tblrec(TwoByte, char.219)
 , {DC}tblrec(TwoByte, char.220)
 , {DD}tblrec(TwoByte, char.221)
 , {DE}tblrec(TwoByte, char.222)
 , {DF}tblrec(TwoByte, char.223)
 , {E0}tblrec(ThreeByte, char.224)
 , {E1}tblrec(ThreeByte, char.225)
 , {E2}tblrec(ThreeByte, char.226)
 , {E3}tblrec(ThreeByte, char.227)
 , {E4}tblrec(ThreeByte, char.228)
 , {E5}tblrec(ThreeByte, char.229)
 , {E6}tblrec(ThreeByte, char.230)
 , {E7}tblrec(ThreeByte, char.231)
 , {E8}tblrec(ThreeByte, char.232)
 , {E9}tblrec(ThreeByte, char.233)
 , {EA}tblrec(ThreeByte, char.234)
 , {EB}tblrec(ThreeByte, char.235)
 , {EC}tblrec(ThreeByte, char.236)
 , {ED}tblrec(ThreeByte, char.237)
 , {EE}tblrec(ThreeByte, char.238)
 , {EF}tblrec(ThreeByte, char.239)
 , {F0}tblrec(FourByte, char.240)
 , {F1}tblrec(FourByte, char.241)
 , {F2}tblrec(FourByte, char.242)
 , {F3}tblrec(FourByte, char.243)
 , {F4}tblrec(FourByte, char.244)
 , {F5}tblrec(FourByte, char.245)
 , {F6}tblrec(FourByte, char.246)
 , {F7}tblrec(FourByte, char.247)
 , {F8}tblrec(Invalid, char.248)
 , {F9}tblrec(Invalid, char.249)
 , {FA}tblrec(Invalid, char.250)
 , {FB}tblrec(Invalid, char.251)
 , {FC}tblrec(Invalid, char.252)
 , {FD}tblrec(Invalid, char.253)
 , {FE}tblrec(Invalid, char.254)
 , {FF}tblrec(Invalid, char.255)
] 