Module wasm

use LEBencoding

use UTF8

use bits

use seq.byte

use seq.seq.byte

use standard

Export type:byte

Export LEBu(i:int) seq.byte

Export LEBs(i:int) seq.byte

Export decodeLEBu(a:seq.byte, i:int) decoderesult

Export decodeLEBs(a:seq.byte, i:int) decoderesult

Export type:decoderesult

Export value(decoderesult) int

Export next(decoderesult) int

Function exportfunc(idx:int, name:word) seq.byte
vector.toseqbyte(emptyUTF8 + decodeword.name) + [tobyte.0x0] + LEBu.idx

Function exportmemory(name:word) seq.byte
vector.toseqbyte(emptyUTF8 + decodeword.name) + [tobyte.0x2, tobyte.0]

Function importfunc(idx:int, modname:word, name:word) seq.byte
vector.toseqbyte(emptyUTF8 + decodeword.modname)
 + vector.toseqbyte(emptyUTF8 + decodeword.name)
 + [tobyte.0]
 + LEBu.idx

Function vector(a:seq.byte) seq.byte
assert n.a < 2^32 report "vector problem^(stacktrace)",
LEBu.n.a + a

Function vector(a:seq.seq.byte) seq.byte
assert n.a < 2^32 report "vector problem"
for acc = LEBu.n.a, @e ∈ a do acc + @e,
acc

Export tobyte(b:bits) byte

Function byte(i:int) byte tobyte.i

function genEnum seq.seq.word
["existingType = byte decodeName = decodeop values = unreachable 0x00 block 0x02 loop 0x03 END 0x0B
br 0x0C brif 0x0D return 0x0F call 0x10 callindirect 0x11 drop 0x1A select 0x1B localget 0x20
localset 0x21 localtee 0x22 globalget 0x23 globalset 0x24 i32load 0x28 i64load 0x29 f32load 0x2A
f64load 0x2B i32load8s 0x2C i32load8u 0x2D i32load16s 0x2E i32load16u 0x2F i64load8s 0x30 i64load8u
0x31 i64load16s 0x32 i64load16u 0x33 i64load32s 0x34 i64load32u 0x35 i32store 0x36 i64store 0x37
f32store 0x38 f64store 0x39 i32store8 0x3A i32store16 0x3B i64store8 0x3C i64store16 0x3D
i64store32 0x3E memorysize 0x3F memorygrow 0x40 i32const 0x41 i64const 0x42 f32const 0x43 f64const
0x44 i32eqz 0x45 i32eq 0x46 i32ne 0x47 i32lts 0x48 i32ltu 0x49 i32gts 0x4A i32gtu 0x4B i32les 0x4C
i32leu 0x4D i32ges 0x4E i32geu 0x4F i64eqz 0x50 i64eq 0x51 i64ne 0x52 i64lts 0x53 i64ltu 0x54
i64gts 0x55 i64gtu 0x56 i64les 0x57 i64leu 0x58 i64ges 0x59 i64geu 0x5A f32eq 0x5B f32ne 0x5C f32lt
0x5D f32gt 0x5E f32le 0x5F f32ge 0x60 f64eq 0x61 f64ne 0x62 f64lt 0x63 f64gt 0x64 f64le 0x65 f64ge
0x66 i32clz 0x67 i32ctz 0x68 i32popcnt 0x69 i32add 0x6A i32sub 0x6B i32mul 0x6C i32divs 0x6D
i32divu 0x6E i32rems 0x6F i32remu 0x70 i32and 0x71 i32or 0x72 i32xor 0x73 i32shl 0x74 i32shrs 0x75
i32shru 0x76 i32rotl 0x77 i32rotr 0x78 i64clz 0x79 i64ctz 0x7A i64popcnt 0x7B i64add 0x7C i64sub
0x7D i64mul 0x7E i64divs 0x7F i64divu 0x80 i64rems 0x81 i64remu 0x82 i64and 0x83 i64or 0x84 i64xor
0x85 i64shl 0x86 i64shrs 0x87 i64shru 0x88 i64rotl 0x89 i64rotr 0x8A f32abs 0x8B f32neg 0x8C
f32ceil 0x8D f32floor 0x8E f32trunc 0x8F f32nearest 0x90 f32sqrt 0x91 f32add 0x92 f32sub 0x93
f32mul 0x94 f32div 0x95 f32min 0x96 f32max 0x97 f32copysign 0x98 f64abs 0x99 f64neg 0x9A f64ceil
0x9B f64floor 0x9C f64trunc 0x9D f64nearest 0x9E f64sqrt 0x9F f64add 0xA0 f64sub 0xA1 f64mul 0xA2
f64div 0xA3 f64min 0xA4 f64max 0xA5 f64copysign 0xA6 i32wrapi64 0xA7 i32truncf32s 0xA8 i32truncf32u
0xA9 i32truncf64s 0xAA i32truncf64u 0xAB i64extendi32s 0xAC i64extendi32u 0xAD i64truncf32s 0xAE
i64truncf32u 0xAF i64truncf64s 0xB0 i64truncf64u 0xB1 f32converti32s 0xB2 f32converti32u 0xB3
f32converti64s 0xB4 f32converti64u 0xB5 f32demotef64 0xB6 f64converti32s 0xB7 f64converti32u 0xB8
f64converti64s 0xB9 f64converti64u 0xBA f64promotef32 0xBB i32reinterpretf32 0xBC i64reinterpretf64
0xBD f32reinterpreti32 0xBE f64reinterpreti64 0xBF i32extend8s 0xC0 i32extend16s 0xC1 i64extend8s
0xC2 i64extend16s 0xC3 i64extend32s 0xC4"]

<<<< Below is auto generated code >>>>

Function unreachable byte tobyte.0

Function block byte tobyte.2

Function loop byte tobyte.3

Function END byte tobyte.11

Function br byte tobyte.12

Function brif byte tobyte.13

Function return byte tobyte.15

Function call byte tobyte.16

Function callindirect byte tobyte.17

Function drop byte tobyte.26

Function select byte tobyte.27

Function localget byte tobyte.32

Function localset byte tobyte.33

Function localtee byte tobyte.34

Function globalget byte tobyte.35

Function globalset byte tobyte.36

Function i32load byte tobyte.40

Function i64load byte tobyte.41

Function f32load byte tobyte.42

Function f64load byte tobyte.43

Function i32load8s byte tobyte.44

Function i32load8u byte tobyte.45

Function i32load16s byte tobyte.46

Function i32load16u byte tobyte.47

Function i64load8s byte tobyte.48

Function i64load8u byte tobyte.49

Function i64load16s byte tobyte.50

Function i64load16u byte tobyte.51

Function i64load32s byte tobyte.52

Function i64load32u byte tobyte.53

Function i32store byte tobyte.54

Function i64store byte tobyte.55

Function f32store byte tobyte.56

Function f64store byte tobyte.57

Function i32store8 byte tobyte.58

Function i32store16 byte tobyte.59

Function i64store8 byte tobyte.60

Function i64store16 byte tobyte.61

Function i64store32 byte tobyte.62

Function memorysize byte tobyte.63

Function memorygrow byte tobyte.64

Function i32const byte tobyte.65

Function i64const byte tobyte.66

Function f32const byte tobyte.67

Function f64const byte tobyte.68

Function i32eqz byte tobyte.69

Function i32eq byte tobyte.70

Function i32ne byte tobyte.71

Function i32lts byte tobyte.72

Function i32ltu byte tobyte.73

Function i32gts byte tobyte.74

Function i32gtu byte tobyte.75

Function i32les byte tobyte.76

Function i32leu byte tobyte.77

Function i32ges byte tobyte.78

Function i32geu byte tobyte.79

Function i64eqz byte tobyte.80

Function i64eq byte tobyte.81

Function i64ne byte tobyte.82

Function i64lts byte tobyte.83

Function i64ltu byte tobyte.84

Function i64gts byte tobyte.85

Function i64gtu byte tobyte.86

Function i64les byte tobyte.87

Function i64leu byte tobyte.88

Function i64ges byte tobyte.89

Function i64geu byte tobyte.90

Function f32eq byte tobyte.91

Function f32ne byte tobyte.92

Function f32lt byte tobyte.93

Function f32gt byte tobyte.94

Function f32le byte tobyte.95

Function f32ge byte tobyte.96

Function f64eq byte tobyte.97

Function f64ne byte tobyte.98

Function f64lt byte tobyte.99

Function f64gt byte tobyte.100

Function f64le byte tobyte.101

Function f64ge byte tobyte.102

Function i32clz byte tobyte.103

Function i32ctz byte tobyte.104

Function i32popcnt byte tobyte.105

Function i32add byte tobyte.106

Function i32sub byte tobyte.107

Function i32mul byte tobyte.108

Function i32divs byte tobyte.109

Function i32divu byte tobyte.110

Function i32rems byte tobyte.111

Function i32remu byte tobyte.112

Function i32and byte tobyte.113

Function i32or byte tobyte.114

Function i32xor byte tobyte.115

Function i32shl byte tobyte.116

Function i32shrs byte tobyte.117

Function i32shru byte tobyte.118

Function i32rotl byte tobyte.119

Function i32rotr byte tobyte.120

Function i64clz byte tobyte.121

Function i64ctz byte tobyte.122

Function i64popcnt byte tobyte.123

Function i64add byte tobyte.124

Function i64sub byte tobyte.125

Function i64mul byte tobyte.126

Function i64divs byte tobyte.127

Function i64divu byte tobyte.128

Function i64rems byte tobyte.129

Function i64remu byte tobyte.130

Function i64and byte tobyte.131

Function i64or byte tobyte.132

Function i64xor byte tobyte.133

Function i64shl byte tobyte.134

Function i64shrs byte tobyte.135

Function i64shru byte tobyte.136

Function i64rotl byte tobyte.137

Function i64rotr byte tobyte.138

Function f32abs byte tobyte.139

Function f32neg byte tobyte.140

Function f32ceil byte tobyte.141

Function f32floor byte tobyte.142

Function f32trunc byte tobyte.143

Function f32nearest byte tobyte.144

Function f32sqrt byte tobyte.145

Function f32add byte tobyte.146

Function f32sub byte tobyte.147

Function f32mul byte tobyte.148

Function f32div byte tobyte.149

Function f32min byte tobyte.150

Function f32max byte tobyte.151

Function f32copysign byte tobyte.152

Function f64abs byte tobyte.153

Function f64neg byte tobyte.154

Function f64ceil byte tobyte.155

Function f64floor byte tobyte.156

Function f64trunc byte tobyte.157

Function f64nearest byte tobyte.158

Function f64sqrt byte tobyte.159

Function f64add byte tobyte.160

Function f64sub byte tobyte.161

Function f64mul byte tobyte.162

Function f64div byte tobyte.163

Function f64min byte tobyte.164

Function f64max byte tobyte.165

Function f64copysign byte tobyte.166

Function i32wrapi64 byte tobyte.167

Function i32truncf32s byte tobyte.168

Function i32truncf32u byte tobyte.169

Function i32truncf64s byte tobyte.170

Function i32truncf64u byte tobyte.171

Function i64extendi32s byte tobyte.172

Function i64extendi32u byte tobyte.173

Function i64truncf32s byte tobyte.174

Function i64truncf32u byte tobyte.175

Function i64truncf64s byte tobyte.176

Function i64truncf64u byte tobyte.177

Function f32converti32s byte tobyte.178

Function f32converti32u byte tobyte.179

Function f32converti64s byte tobyte.180

Function f32converti64u byte tobyte.181

Function f32demotef64 byte tobyte.182

Function f64converti32s byte tobyte.183

Function f64converti32u byte tobyte.184

Function f64converti64s byte tobyte.185

Function f64converti64u byte tobyte.186

Function f64promotef32 byte tobyte.187

Function i32reinterpretf32 byte tobyte.188

Function i64reinterpretf64 byte tobyte.189

Function f32reinterpreti32 byte tobyte.190

Function f64reinterpreti64 byte tobyte.191

Function i32extend8s byte tobyte.192

Function i32extend16s byte tobyte.193

Function i64extend8s byte tobyte.194

Function i64extend16s byte tobyte.195

Function i64extend32s byte tobyte.196

Function decodeop(code:byte) seq.word
let discard = [
 unreachable
 , block
 , loop
 , END
 , br
 , brif
 , return
 , call
 , callindirect
 , drop
 , select
 , localget
 , localset
 , localtee
 , globalget
 , globalset
 , i32load
 , i64load
 , f32load
 , f64load
 , i32load8s
 , i32load8u
 , i32load16s
 , i32load16u
 , i64load8s
 , i64load8u
 , i64load16s
 , i64load16u
 , i64load32s
 , i64load32u
 , i32store
 , i64store
 , f32store
 , f64store
 , i32store8
 , i32store16
 , i64store8
 , i64store16
 , i64store32
 , memorysize
 , memorygrow
 , i32const
 , i64const
 , f32const
 , f64const
 , i32eqz
 , i32eq
 , i32ne
 , i32lts
 , i32ltu
 , i32gts
 , i32gtu
 , i32les
 , i32leu
 , i32ges
 , i32geu
 , i64eqz
 , i64eq
 , i64ne
 , i64lts
 , i64ltu
 , i64gts
 , i64gtu
 , i64les
 , i64leu
 , i64ges
 , i64geu
 , f32eq
 , f32ne
 , f32lt
 , f32gt
 , f32le
 , f32ge
 , f64eq
 , f64ne
 , f64lt
 , f64gt
 , f64le
 , f64ge
 , i32clz
 , i32ctz
 , i32popcnt
 , i32add
 , i32sub
 , i32mul
 , i32divs
 , i32divu
 , i32rems
 , i32remu
 , i32and
 , i32or
 , i32xor
 , i32shl
 , i32shrs
 , i32shru
 , i32rotl
 , i32rotr
 , i64clz
 , i64ctz
 , i64popcnt
 , i64add
 , i64sub
 , i64mul
 , i64divs
 , i64divu
 , i64rems
 , i64remu
 , i64and
 , i64or
 , i64xor
 , i64shl
 , i64shrs
 , i64shru
 , i64rotl
 , i64rotr
 , f32abs
 , f32neg
 , f32ceil
 , f32floor
 , f32trunc
 , f32nearest
 , f32sqrt
 , f32add
 , f32sub
 , f32mul
 , f32div
 , f32min
 , f32max
 , f32copysign
 , f64abs
 , f64neg
 , f64ceil
 , f64floor
 , f64trunc
 , f64nearest
 , f64sqrt
 , f64add
 , f64sub
 , f64mul
 , f64div
 , f64min
 , f64max
 , f64copysign
 , i32wrapi64
 , i32truncf32s
 , i32truncf32u
 , i32truncf64s
 , i32truncf64u
 , i64extendi32s
 , i64extendi32u
 , i64truncf32s
 , i64truncf32u
 , i64truncf64s
 , i64truncf64u
 , f32converti32s
 , f32converti32u
 , f32converti64s
 , f32converti64u
 , f32demotef64
 , f64converti32s
 , f64converti32u
 , f64converti64s
 , f64converti64u
 , f64promotef32
 , i32reinterpretf32
 , i64reinterpretf64
 , f32reinterpreti32
 , f64reinterpreti64
 , i32extend8s
 , i32extend16s
 , i64extend8s
 , i64extend16s
 , i64extend32s
]
let i = toint.code,
if between(i + 1, 1, 197) then
 let r = [
  (i + 1)
  #"unreachable ? block loop ? ? ? ? ? ? ? END br brif ? return call callindirect ? ? ? ? ? ? ? ? drop
  select ? ? ? ? localget localset localtee globalget globalset ? ? ? i32load i64load f32load f64load
  i32load8s i32load8u i32load16s i32load16u i64load8s i64load8u i64load16s i64load16u i64load32s
  i64load32u i32store i64store f32store f64store i32store8 i32store16 i64store8 i64store16 i64store32
  memorysize memorygrow i32const i64const f32const f64const i32eqz i32eq i32ne i32lts i32ltu i32gts
  i32gtu i32les i32leu i32ges i32geu i64eqz i64eq i64ne i64lts i64ltu i64gts i64gtu i64les i64leu
  i64ges i64geu f32eq f32ne f32lt f32gt f32le f32ge f64eq f64ne f64lt f64gt f64le f64ge i32clz i32ctz
  i32popcnt i32add i32sub i32mul i32divs i32divu i32rems i32remu i32and i32or i32xor i32shl i32shrs
  i32shru i32rotl i32rotr i64clz i64ctz i64popcnt i64add i64sub i64mul i64divs i64divu i64rems
  i64remu i64and i64or i64xor i64shl i64shrs i64shru i64rotl i64rotr f32abs f32neg f32ceil f32floor
  f32trunc f32nearest f32sqrt f32add f32sub f32mul f32div f32min f32max f32copysign f64abs f64neg
  f64ceil f64floor f64trunc f64nearest f64sqrt f64add f64sub f64mul f64div f64min f64max f64copysign
  i32wrapi64 i32truncf32s i32truncf32u i32truncf64s i32truncf64u i64extendi32s i64extendi32u
  i64truncf32s i64truncf32u i64truncf64s i64truncf64u f32converti32s f32converti32u f32converti64s
  f32converti64u f32demotef64 f64converti32s f64converti32u f64converti64s f64converti64u
  f64promotef32 i32reinterpretf32 i64reinterpretf64 f32reinterpreti32 f64reinterpreti64 i32extend8s
  i32extend16s i64extend8s i64extend16s i64extend32s"
 ],
 if r ≠ "?" then r else "byte." + toword.i
else "byte." + toword.i 