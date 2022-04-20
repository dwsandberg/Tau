#!/usr/local/bin/tau ; use wasm; wasmbytes

Module wasm

use UTF8

use bits

use standard

use seq.byte

use seq.char

use seq.decoderesult

use set.int

use seq.seq.byte

Export type:byte




Function testLEB seq.word
let r = 
 [tobyte.127, tobyte.128, tobyte.1, tobyte.128, tobyte.128
 , tobyte.4, tobyte.229, tobyte.142, tobyte.38, tobyte.255
 , tobyte.0, tobyte.192, tobyte.187, tobyte.120]
let d1 = decodeLEBunsigned(r, 1)
let d2 = decodeLEBunsigned(r, next.d1)
let d3 = decodeLEBunsigned(r, next.d2)
let d4 = decodeLEBunsigned(r, next.d3)
let d5 = decodeLEBsigned(r, next.d4)
let d6 = decodeLEBsigned(r, next.d5)
if LEB.127 + LEB.128 + LEB.2^16 + LEB.624485 + LEBsigned.127 + LEBsigned.-123456 = r
∧ for acc = empty:seq.int, @e ∈[d1, d2, d3, d4, d5, d6]do acc + value.@e /for(acc)
= [127, 128, 65536, 624485, 127, -123456]then
 "PASS"
else"FAIL"

Function decodeLEBunsigned(a:seq.byte, i:int)decoderesult decodeLEB(a, i, 0x0, 0)

Function decodeLEBsigned(a:seq.byte, i:int)decoderesult
let r = decodeLEB(a, i, 0x0, 0)
let byte = tobits.a_(next.r - 1)
if(byte ∧ 0x40) = 0x0 then r
else decoderesult(toint(bits.value.r ∨ tobits.-1 << ((next.r - i) * 7)), next.r)

type decoderesult is value:int, next:int

Export type:decoderesult

Export value(decoderesult)int

Export next(decoderesult)int

function decodeLEB(a:seq.byte, i:int, result:bits, shift:int)decoderesult
let byte = tobits.a_i
let c = byte ∧ 0x7F
let newresult = result ∨ c << shift
if c = byte then decoderesult(toint.newresult, i + 1)
else decodeLEB(a, i + 1, newresult, shift + 7)

Function LEB(i:int)seq.byte LEB(bits.0, bits.i, empty:seq.byte)

Function LEBsigned(i:int)seq.byte LEB(bits.64, bits.i, empty:seq.byte)

function LEB(signbit:bits, value:bits, result:seq.byte)seq.byte
let byte = value ∧ bits.127
let value1 = if toint.value < 0 then bits.-1 << (64 - 7) ∨ value >> 7 else value >> 7
if toint.value1 = 0 ∧ toint(byte ∧ signbit) = 0 then result + tobyte.byte
else if toint.value1 = -1 ∧ toint.byte ≥ toint.signbit then result + tobyte.byte
else LEB(signbit, value1, result + tobyte(byte ∨ bits.128))

Function exportfunc(idx:int, name:word)seq.byte vector.toseqbyte(emptyUTF8 + decodeword.name) + [tobyte.0x0] + LEB.idx

Function exportmemory(name:word)seq.byte vector.toseqbyte(emptyUTF8 + decodeword.name) + [tobyte.0x2, tobyte.0]

Function importfunc(idx:int, modname:word, name:word)seq.byte
vector.toseqbyte(emptyUTF8 + decodeword.modname) + vector.toseqbyte(emptyUTF8 + decodeword.name)
+ [tobyte.0]
+ LEB.idx

Function vector(a:seq.byte)seq.byte
assert length.a < 2^32 report"vector problem" + stacktrace
LEB.length.a + a

Function vector(a:seq.seq.byte)seq.byte
assert length.a < 2^32 report"vector problem"
for acc = LEB.length.a, @e ∈ a do acc + @e /for(acc)

function tobytea(a:seq.char)seq.byte
{handles ascii only}
for acc = empty:seq.byte, @e ∈ a do acc + tobyte.toint.@e /for(acc)

Function tobyte(b:bits)byte tobyte.toint.b

Function wasmbytes seq.word
{used to generate code that follows this function in this package}
let data = 
 "00 unreachable 02 block 03 loop 0B END 0C br 0D brif 0F return 10 call 11 callindirect 1A drop 1B select 20 localget 21 localset 
22 localtee 23 globalget 24 globalset 28 i32load 29 i64load 2A f32load 2B f64load 2C i32load8s 2D i32load8u 2E i32load16s 
2F i32load16u 30 i64load8s 31 i64load8u 32 i64load16s 33 i64load16u 34 i64load32s 35 i64load32u 36 i32store 37 i64store 
38 f32store 39 f64store 3A i32store8 3B i32store16 3C i64store8 3D i64store16 3E i64store32 3F memorysize 40 memorygrow 
41 i32const 42 i64const 43 f32const 44 f64const 45 i32eqz 46 i32eq 47 i32ne 48 i32lts 49 i32ltu 4A i32gts 4B i32gtu 4C i32les 
4D i32leu 4E i32ges 4F i32geu 50 i64eqz 51 i64eq 52 i64ne 53 i64lts 54 i64ltu 55 i64gts 56 i64gtu 57 i64les 58 i64leu 59 i64ges 
5A i64geu 5B f32eq 5C f32ne 5D f32lt 5E f32gt 5F f32le 60 f32ge 61 f64eq 62 f64ne 63 f64lt 64 f64gt 65 f64le 66 f64ge 67 i32clz 68 
i32ctz 69 i32popcnt 6A i32add 6B i32sub 6C i32mul 6D i32divs 6E i32divu 6F i32rems 70 i32remu 71 i32and 72 i32or 73 i32xor 74 
i32shl 75 i32shrs 76 i32shru 77 i32rotl 78 i32rotr 79 i64clz 7A i64ctz 7B i64popcnt 7C i64add 7D i64sub 7E i64mul 7F i64divs 
80 i64divu 81 i64rems 82 i64remu 83 i64and 84 i64or 85 i64xor 86 i64shl 87 i64shrs 88 i64shru 89 i64rotl 8A i64rotr 8B f32abs 
8C f32neg 8D f32ceil 8E f32floor 8F f32trunc 90 f32nearest 91 f32sqrt 92 f32add 93 f32sub 94 f32mul 95 f32div 96 f32min 97 f32max 
98 f32copysign 99 f64abs 9A f64neg 9B f64ceil 9C f64floor 9D f64trunc 9E f64nearest 9F f64sqrt A0 f64add A1 f64sub A2 f64mul 
A3 f64div A4 f64min A5 f64max A6 f64copysign A7 i32wrapi64 A8 i32truncf32s A9 i32truncf32u AA i32truncf64s AB i32truncf64u 
AC i64extendi32s AD i64extendi32u AE i64truncf32s AF i64truncf32u B0 i64truncf64s B1 i64truncf64u B2 f32converti32s 
B3 f32converti32u B4 f32converti64s B5 f32converti64u B6 f32demotef64 B7 f64converti32s B8 f64converti32u B9 f64converti64s 
BA f64converti64u BB f64promotef32 BC i32reinterpretf32 BD i64reinterpretf64 BE f32reinterpreti32 BF f64reinterpreti64 
C0 i32extend8s C1 i32extend16s C2 i64extend8s C3 i64extend16s C4 i64extend32s"
let z = 
 for acc = "", @i = 1, @e ∈ data do
  next(acc
  + if @i mod 2 = 1 then
   " /br else if c=" + merge("0x" + @e) + "then first.'" + data_(@i + 1)
   + "'"
  else""
  , @i + 1
  )
 /for(acc)
" /p Function decodeop(cc:byte)word  /br let c=tobits.cc  /br" + z << 2
+ "else first.' ? '"
+ for acc = "", @i = 1, @e ∈ data do
 next(acc
 + if @i mod 2 = 1 then
  " /p Function" + data_(@i + 1) + "byte tobyte." + merge("0x" + @e)
 else""
 , @i + 1
 )
/for(acc)

Function decodeop(cc:byte)word
let c = tobits.cc
if c = 0x00 then first."unreachable"
else if c = 0x02 then first."block"
else if c = 0x03 then first."loop"
else if c = 0x0B then first."END"
else if c = 0x0C then first."br"
else if c = 0x0D then first."brif"
else if c = 0x0F then first."return"
else if c = 0x10 then first."call"
else if c = 0x11 then first."callindirect"
else if c = 0x1A then first."drop"
else if c = 0x1B then first."select"
else if c = 0x20 then first."localget"
else if c = 0x21 then first."localset"
else if c = 0x22 then first."localtee"
else if c = 0x23 then first."globalget"
else if c = 0x24 then first."globalset"
else if c = 0x28 then first."i32load"
else if c = 0x29 then first."i64load"
else if c = 0x2A then first."f32load"
else if c = 0x2B then first."f64load"
else if c = 0x2C then first."i32load8s"
else if c = 0x2D then first."i32load8u"
else if c = 0x2E then first."i32load16s"
else if c = 0x2F then first."i32load16u"
else if c = 0x30 then first."i64load8s"
else if c = 0x31 then first."i64load8u"
else if c = 0x32 then first."i64load16s"
else if c = 0x33 then first."i64load16u"
else if c = 0x34 then first."i64load32s"
else if c = 0x35 then first."i64load32u"
else if c = 0x36 then first."i32store"
else if c = 0x37 then first."i64store"
else if c = 0x38 then first."f32store"
else if c = 0x39 then first."f64store"
else if c = 0x3A then first."i32store8"
else if c = 0x3B then first."i32store16"
else if c = 0x3C then first."i64store8"
else if c = 0x3D then first."i64store16"
else if c = 0x3E then first."i64store32"
else if c = 0x3F then first."memorysize"
else if c = 0x40 then first."memorygrow"
else if c = 0x41 then first."i32const"
else if c = 0x42 then first."i64const"
else if c = 0x43 then first."f32const"
else if c = 0x44 then first."f64const"
else if c = 0x45 then first."i32eqz"
else if c = 0x46 then first."i32eq"
else if c = 0x47 then first."i32ne"
else if c = 0x48 then first."i32lts"
else if c = 0x49 then first."i32ltu"
else if c = 0x4A then first."i32gts"
else if c = 0x4B then first."i32gtu"
else if c = 0x4C then first."i32les"
else if c = 0x4D then first."i32leu"
else if c = 0x4E then first."i32ges"
else if c = 0x4F then first."i32geu"
else if c = 0x50 then first."i64eqz"
else if c = 0x51 then first."i64eq"
else if c = 0x52 then first."i64ne"
else if c = 0x53 then first."i64lts"
else if c = 0x54 then first."i64ltu"
else if c = 0x55 then first."i64gts"
else if c = 0x56 then first."i64gtu"
else if c = 0x57 then first."i64les"
else if c = 0x58 then first."i64leu"
else if c = 0x59 then first."i64ges"
else if c = 0x5A then first."i64geu"
else if c = 0x5B then first."f32eq"
else if c = 0x5C then first."f32ne"
else if c = 0x5D then first."f32lt"
else if c = 0x5E then first."f32gt"
else if c = 0x5F then first."f32le"
else if c = 0x60 then first."f32ge"
else if c = 0x61 then first."f64eq"
else if c = 0x62 then first."f64ne"
else if c = 0x63 then first."f64lt"
else if c = 0x64 then first."f64gt"
else if c = 0x65 then first."f64le"
else if c = 0x66 then first."f64ge"
else if c = 0x67 then first."i32clz"
else if c = 0x68 then first."i32ctz"
else if c = 0x69 then first."i32popcnt"
else if c = 0x6A then first."i32add"
else if c = 0x6B then first."i32sub"
else if c = 0x6C then first."i32mul"
else if c = 0x6D then first."i32divs"
else if c = 0x6E then first."i32divu"
else if c = 0x6F then first."i32rems"
else if c = 0x70 then first."i32remu"
else if c = 0x71 then first."i32and"
else if c = 0x72 then first."i32or"
else if c = 0x73 then first."i32xor"
else if c = 0x74 then first."i32shl"
else if c = 0x75 then first."i32shrs"
else if c = 0x76 then first."i32shru"
else if c = 0x77 then first."i32rotl"
else if c = 0x78 then first."i32rotr"
else if c = 0x79 then first."i64clz"
else if c = 0x7A then first."i64ctz"
else if c = 0x7B then first."i64popcnt"
else if c = 0x7C then first."i64add"
else if c = 0x7D then first."i64sub"
else if c = 0x7E then first."i64mul"
else if c = 0x7F then first."i64divs"
else if c = 0x80 then first."i64divu"
else if c = 0x81 then first."i64rems"
else if c = 0x82 then first."i64remu"
else if c = 0x83 then first."i64and"
else if c = 0x84 then first."i64or"
else if c = 0x85 then first."i64xor"
else if c = 0x86 then first."i64shl"
else if c = 0x87 then first."i64shrs"
else if c = 0x88 then first."i64shru"
else if c = 0x89 then first."i64rotl"
else if c = 0x8A then first."i64rotr"
else if c = 0x8B then first."f32abs"
else if c = 0x8C then first."f32neg"
else if c = 0x8D then first."f32ceil"
else if c = 0x8E then first."f32floor"
else if c = 0x8F then first."f32trunc"
else if c = 0x90 then first."f32nearest"
else if c = 0x91 then first."f32sqrt"
else if c = 0x92 then first."f32add"
else if c = 0x93 then first."f32sub"
else if c = 0x94 then first."f32mul"
else if c = 0x95 then first."f32div"
else if c = 0x96 then first."f32min"
else if c = 0x97 then first."f32max"
else if c = 0x98 then first."f32copysign"
else if c = 0x99 then first."f64abs"
else if c = 0x9A then first."f64neg"
else if c = 0x9B then first."f64ceil"
else if c = 0x9C then first."f64floor"
else if c = 0x9D then first."f64trunc"
else if c = 0x9E then first."f64nearest"
else if c = 0x9F then first."f64sqrt"
else if c = 0xA0 then first."f64add"
else if c = 0xA1 then first."f64sub"
else if c = 0xA2 then first."f64mul"
else if c = 0xA3 then first."f64div"
else if c = 0xA4 then first."f64min"
else if c = 0xA5 then first."f64max"
else if c = 0xA6 then first."f64copysign"
else if c = 0xA7 then first."i32wrapi64"
else if c = 0xA8 then first."i32truncf32s"
else if c = 0xA9 then first."i32truncf32u"
else if c = 0xAA then first."i32truncf64s"
else if c = 0xAB then first."i32truncf64u"
else if c = 0xAC then first."i64extendi32s"
else if c = 0xAD then first."i64extendi32u"
else if c = 0xAE then first."i64truncf32s"
else if c = 0xAF then first."i64truncf32u"
else if c = 0xB0 then first."i64truncf64s"
else if c = 0xB1 then first."i64truncf64u"
else if c = 0xB2 then first."f32converti32s"
else if c = 0xB3 then first."f32converti32u"
else if c = 0xB4 then first."f32converti64s"
else if c = 0xB5 then first."f32converti64u"
else if c = 0xB6 then first."f32demotef64"
else if c = 0xB7 then first."f64converti32s"
else if c = 0xB8 then first."f64converti32u"
else if c = 0xB9 then first."f64converti64s"
else if c = 0xBA then first."f64converti64u"
else if c = 0xBB then first."f64promotef32"
else if c = 0xBC then first."i32reinterpretf32"
else if c = 0xBD then first."i64reinterpretf64"
else if c = 0xBE then first."f32reinterpreti32"
else if c = 0xBF then first."f64reinterpreti64"
else if c = 0xC0 then first."i32extend8s"
else if c = 0xC1 then first."i32extend16s"
else if c = 0xC2 then first."i64extend8s"
else if c = 0xC3 then first."i64extend16s"
else if c = 0xC4 then first."i64extend32s"
else{first.' ? '}merge("?" + toword.toint.c)

Function unreachable byte tobyte.0x00

Function block byte tobyte.0x02

Function loop byte tobyte.0x03

Function END byte tobyte.0x0B

Function br byte tobyte.0x0C

Function brif byte tobyte.0x0D

Function return byte tobyte.0x0F

Function call byte tobyte.0x10

Function callindirect byte tobyte.0x11

Function drop byte tobyte.0x1A

Function select byte tobyte.0x1B

Function localget byte tobyte.0x20

Function localset byte tobyte.0x21

Function localtee byte tobyte.0x22

Function globalget byte tobyte.0x23

Function globalset byte tobyte.0x24

Function i32load byte tobyte.0x28

Function i64load byte tobyte.0x29

Function f32load byte tobyte.0x2A

Function f64load byte tobyte.0x2B

Function i32load8s byte tobyte.0x2C

Function i32load8u byte tobyte.0x2D

Function i32load16s byte tobyte.0x2E

Function i32load16u byte tobyte.0x2F

Function i64load8s byte tobyte.0x30

Function i64load8u byte tobyte.0x31

Function i64load16s byte tobyte.0x32

Function i64load16u byte tobyte.0x33

Function i64load32s byte tobyte.0x34

Function i64load32u byte tobyte.0x35

Function i32store byte tobyte.0x36

Function i64store byte tobyte.0x37

Function f32store byte tobyte.0x38

Function f64store byte tobyte.0x39

Function i32store8 byte tobyte.0x3A

Function i32store16 byte tobyte.0x3B

Function i64store8 byte tobyte.0x3C

Function i64store16 byte tobyte.0x3D

Function i64store32 byte tobyte.0x3E

Function memorysize byte tobyte.0x3F

Function memorygrow byte tobyte.0x40

Function i32const byte tobyte.0x41

Function i64const byte tobyte.0x42

Function f32const byte tobyte.0x43

Function f64const byte tobyte.0x44

Function i32eqz byte tobyte.0x45

Function i32eq byte tobyte.0x46

Function i32ne byte tobyte.0x47

Function i32lts byte tobyte.0x48

Function i32ltu byte tobyte.0x49

Function i32gts byte tobyte.0x4A

Function i32gtu byte tobyte.0x4B

Function i32les byte tobyte.0x4C

Function i32leu byte tobyte.0x4D

Function i32ges byte tobyte.0x4E

Function i32geu byte tobyte.0x4F

Function i64eqz byte tobyte.0x50

Function i64eq byte tobyte.0x51

Function i64ne byte tobyte.0x52

Function i64lts byte tobyte.0x53

Function i64ltu byte tobyte.0x54

Function i64gts byte tobyte.0x55

Function i64gtu byte tobyte.0x56

Function i64les byte tobyte.0x57

Function i64leu byte tobyte.0x58

Function i64ges byte tobyte.0x59

Function i64geu byte tobyte.0x5A

Function f32eq byte tobyte.0x5B

Function f32ne byte tobyte.0x5C

Function f32lt byte tobyte.0x5D

Function f32gt byte tobyte.0x5E

Function f32le byte tobyte.0x5F

Function f32ge byte tobyte.0x60

Function f64eq byte tobyte.0x61

Function f64ne byte tobyte.0x62

Function f64lt byte tobyte.0x63

Function f64gt byte tobyte.0x64

Function f64le byte tobyte.0x65

Function f64ge byte tobyte.0x66

Function i32clz byte tobyte.0x67

Function i32ctz byte tobyte.0x68

Function i32popcnt byte tobyte.0x69

Function i32add byte tobyte.0x6A

Function i32sub byte tobyte.0x6B

Function i32mul byte tobyte.0x6C

Function i32divs byte tobyte.0x6D

Function i32divu byte tobyte.0x6E

Function i32rems byte tobyte.0x6F

Function i32remu byte tobyte.0x70

Function i32and byte tobyte.0x71

Function i32or byte tobyte.0x72

Function i32xor byte tobyte.0x73

Function i32shl byte tobyte.0x74

Function i32shrs byte tobyte.0x75

Function i32shru byte tobyte.0x76

Function i32rotl byte tobyte.0x77

Function i32rotr byte tobyte.0x78

Function i64clz byte tobyte.0x79

Function i64ctz byte tobyte.0x7A

Function i64popcnt byte tobyte.0x7B

Function i64add byte tobyte.0x7C

Function i64sub byte tobyte.0x7D

Function i64mul byte tobyte.0x7E

Function i64divs byte tobyte.0x7F

Function i64divu byte tobyte.0x80

Function i64rems byte tobyte.0x81

Function i64remu byte tobyte.0x82

Function i64and byte tobyte.0x83

Function i64or byte tobyte.0x84

Function i64xor byte tobyte.0x85

Function i64shl byte tobyte.0x86

Function i64shrs byte tobyte.0x87

Function i64shru byte tobyte.0x88

Function i64rotl byte tobyte.0x89

Function i64rotr byte tobyte.0x8A

Function f32abs byte tobyte.0x8B

Function f32neg byte tobyte.0x8C

Function f32ceil byte tobyte.0x8D

Function f32floor byte tobyte.0x8E

Function f32trunc byte tobyte.0x8F

Function f32nearest byte tobyte.0x90

Function f32sqrt byte tobyte.0x91

Function f32add byte tobyte.0x92

Function f32sub byte tobyte.0x93

Function f32mul byte tobyte.0x94

Function f32div byte tobyte.0x95

Function f32min byte tobyte.0x96

Function f32max byte tobyte.0x97

Function f32copysign byte tobyte.0x98

Function f64abs byte tobyte.0x99

Function f64neg byte tobyte.0x9A

Function f64ceil byte tobyte.0x9B

Function f64floor byte tobyte.0x9C

Function f64trunc byte tobyte.0x9D

Function f64nearest byte tobyte.0x9E

Function f64sqrt byte tobyte.0x9F

Function f64add byte tobyte.0xA0

Function f64sub byte tobyte.0xA1

Function f64mul byte tobyte.0xA2

Function f64div byte tobyte.0xA3

Function f64min byte tobyte.0xA4

Function f64max byte tobyte.0xA5

Function f64copysign byte tobyte.0xA6

Function i32wrapi64 byte tobyte.0xA7

Function i32truncf32s byte tobyte.0xA8

Function i32truncf32u byte tobyte.0xA9

Function i32truncf64s byte tobyte.0xAA

Function i32truncf64u byte tobyte.0xAB

Function i64extendi32s byte tobyte.0xAC

Function i64extendi32u byte tobyte.0xAD

Function i64truncf32s byte tobyte.0xAE

Function i64truncf32u byte tobyte.0xAF

Function i64truncf64s byte tobyte.0xB0

Function i64truncf64u byte tobyte.0xB1

Function f32converti32s byte tobyte.0xB2

Function f32converti32u byte tobyte.0xB3

Function f32converti64s byte tobyte.0xB4

Function f32converti64u byte tobyte.0xB5

Function f32demotef64 byte tobyte.0xB6

Function f64converti32s byte tobyte.0xB7

Function f64converti32u byte tobyte.0xB8

Function f64converti64s byte tobyte.0xB9

Function f64converti64u byte tobyte.0xBA

Function f64promotef32 byte tobyte.0xBB

Function i32reinterpretf32 byte tobyte.0xBC

Function i64reinterpretf64 byte tobyte.0xBD

Function f32reinterpreti32 byte tobyte.0xBE

Function f64reinterpreti64 byte tobyte.0xBF

Function i32extend8s byte tobyte.0xC0

Function i32extend16s byte tobyte.0xC1

Function i64extend8s byte tobyte.0xC2

Function i64extend16s byte tobyte.0xC3

Function i64extend32s byte tobyte.0xC4 