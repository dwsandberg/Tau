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
assert length.a < 2^32 report "vector problem $(stacktrace)",
LEBu.length.a + a

Function vector(a:seq.seq.byte) seq.byte
assert length.a < 2^32 report "vector problem",
for acc = LEBu.length.a, @e ∈ a do acc + @e /do acc

Export tobyte(b:bits) byte

Function byte(i:int) byte tobyte.i

enumerationtype = byte decodename = decodeop flags = nodecs withvalues data = 00 unreachable 02 block
03 loop 0B END 0C br 0D brif 0F return 10 call 11 callindirect 1A drop 1B select 20 localget 21 localset
22 localtee 23 globalget 24 globalset 28 i32load 29 i64load 2A f32load 2B f64load 2C i32load8s 2D i32load8u
2E i32load16s 2F i32load16u 30 i64load8s 31 i64load8u 32 i64load16s 33 i64load16u 34 i64load32s 35 i64load32u
36 i32store 37 i64store 38 f32store 39 f64store 3A i32store8 3B i32store16 3C i64store8 3D i64store16
3E i64store32 3F memorysize 40 memorygrow 41 i32const 42 i64const 43 f32const 44 f64const 45 i32eqz 46
i32eq 47 i32ne 48 i32lts 49 i32ltu 4A i32gts 4B i32gtu 4C i32les 4D i32leu 4E i32ges 4F i32geu 50 i64eqz
51 i64eq 52 i64ne 53 i64lts 54 i64ltu 55 i64gts 56 i64gtu 57 i64les 58 i64leu 59 i64ges 5A i64geu 5B
f32eq 5C f32ne 5D f32lt 5E f32gt 5F f32le 60 f32ge 61 f64eq 62 f64ne 63 f64lt 64 f64gt 65 f64le 66 f64ge
67 i32clz 68 i32ctz 69 i32popcnt 6A i32add 6B i32sub 6C i32mul 6D i32divs 6E i32divu 6F i32rems 70 i32remu
71 i32and 72 i32or 73 i32xor 74 i32shl 75 i32shrs 76 i32shru 77 i32rotl 78 i32rotr 79 i64clz 7A i64ctz
7B i64popcnt 7C i64add 7D i64sub 7E i64mul 7F i64divs 80 i64divu 81 i64rems 82 i64remu 83 i64and 84 i64or
85 i64xor 86 i64shl 87 i64shrs 88 i64shru 89 i64rotl 8A i64rotr 8B f32abs 8C f32neg 8D f32ceil 8E f32floor
8F f32trunc 90 f32nearest 91 f32sqrt 92 f32add 93 f32sub 94 f32mul 95 f32div 96 f32min 97 f32max 98 f32copysign
99 f64abs 9A f64neg 9B f64ceil 9C f64floor 9D f64trunc 9E f64nearest 9F f64sqrt A0 f64add A1 f64sub A2
f64mul A3 f64div A4 f64min A5 f64max A6 f64copysign A7 i32wrapi64 A8 i32truncf32s A9 i32truncf32u AA
i32truncf64s AB i32truncf64u AC i64extendi32s AD i64extendi32u AE i64truncf32s AF i64truncf32u B0 i64truncf64s
B1 i64truncf64u B2 f32converti32s B3 f32converti32u B4 f32converti64s B5 f32converti64u B6 f32demotef64
B7 f64converti32s B8 f64converti32u B9 f64converti64s BA f64converti64u BB f64promotef32 BC i32reinterpretf32
BD i64reinterpretf64 BE f32reinterpreti32 BF f64reinterpreti64 C0 i32extend8s C1 i32extend16s C2 i64extend8s
C3 i64extend16s C4 i64extend32s

The data below this line was auto generated.

_________________________________________

Function unreachable byte byte.0

Function block byte byte.2

Function loop byte byte.3

Function END byte byte.11

Function br byte byte.12

Function brif byte byte.13

Function return byte byte.15

Function call byte byte.16

Function callindirect byte byte.17

Function drop byte byte.26

Function select byte byte.27

Function localget byte byte.32

Function localset byte byte.33

Function localtee byte byte.34

Function globalget byte byte.35

Function globalset byte byte.36

Function i32load byte byte.40

Function i64load byte byte.41

Function f32load byte byte.42

Function f64load byte byte.43

Function i32load8s byte byte.44

Function i32load8u byte byte.45

Function i32load16s byte byte.46

Function i32load16u byte byte.47

Function i64load8s byte byte.48

Function i64load8u byte byte.49

Function i64load16s byte byte.50

Function i64load16u byte byte.51

Function i64load32s byte byte.52

Function i64load32u byte byte.53

Function i32store byte byte.54

Function i64store byte byte.55

Function f32store byte byte.56

Function f64store byte byte.57

Function i32store8 byte byte.58

Function i32store16 byte byte.59

Function i64store8 byte byte.60

Function i64store16 byte byte.61

Function i64store32 byte byte.62

Function memorysize byte byte.63

Function memorygrow byte byte.64

Function i32const byte byte.65

Function i64const byte byte.66

Function f32const byte byte.67

Function f64const byte byte.68

Function i32eqz byte byte.69

Function i32eq byte byte.70

Function i32ne byte byte.71

Function i32lts byte byte.72

Function i32ltu byte byte.73

Function i32gts byte byte.74

Function i32gtu byte byte.75

Function i32les byte byte.76

Function i32leu byte byte.77

Function i32ges byte byte.78

Function i32geu byte byte.79

Function i64eqz byte byte.80

Function i64eq byte byte.81

Function i64ne byte byte.82

Function i64lts byte byte.83

Function i64ltu byte byte.84

Function i64gts byte byte.85

Function i64gtu byte byte.86

Function i64les byte byte.87

Function i64leu byte byte.88

Function i64ges byte byte.89

Function i64geu byte byte.90

Function f32eq byte byte.91

Function f32ne byte byte.92

Function f32lt byte byte.93

Function f32gt byte byte.94

Function f32le byte byte.95

Function f32ge byte byte.96

Function f64eq byte byte.97

Function f64ne byte byte.98

Function f64lt byte byte.99

Function f64gt byte byte.100

Function f64le byte byte.101

Function f64ge byte byte.102

Function i32clz byte byte.103

Function i32ctz byte byte.104

Function i32popcnt byte byte.105

Function i32add byte byte.106

Function i32sub byte byte.107

Function i32mul byte byte.108

Function i32divs byte byte.109

Function i32divu byte byte.110

Function i32rems byte byte.111

Function i32remu byte byte.112

Function i32and byte byte.113

Function i32or byte byte.114

Function i32xor byte byte.115

Function i32shl byte byte.116

Function i32shrs byte byte.117

Function i32shru byte byte.118

Function i32rotl byte byte.119

Function i32rotr byte byte.120

Function i64clz byte byte.121

Function i64ctz byte byte.122

Function i64popcnt byte byte.123

Function i64add byte byte.124

Function i64sub byte byte.125

Function i64mul byte byte.126

Function i64divs byte byte.127

Function i64divu byte byte.128

Function i64rems byte byte.129

Function i64remu byte byte.130

Function i64and byte byte.131

Function i64or byte byte.132

Function i64xor byte byte.133

Function i64shl byte byte.134

Function i64shrs byte byte.135

Function i64shru byte byte.136

Function i64rotl byte byte.137

Function i64rotr byte byte.138

Function f32abs byte byte.139

Function f32neg byte byte.140

Function f32ceil byte byte.141

Function f32floor byte byte.142

Function f32trunc byte byte.143

Function f32nearest byte byte.144

Function f32sqrt byte byte.145

Function f32add byte byte.146

Function f32sub byte byte.147

Function f32mul byte byte.148

Function f32div byte byte.149

Function f32min byte byte.150

Function f32max byte byte.151

Function f32copysign byte byte.152

Function f64abs byte byte.153

Function f64neg byte byte.154

Function f64ceil byte byte.155

Function f64floor byte byte.156

Function f64trunc byte byte.157

Function f64nearest byte byte.158

Function f64sqrt byte byte.159

Function f64add byte byte.160

Function f64sub byte byte.161

Function f64mul byte byte.162

Function f64div byte byte.163

Function f64min byte byte.164

Function f64max byte byte.165

Function f64copysign byte byte.166

Function i32wrapi64 byte byte.167

Function i32truncf32s byte byte.168

Function i32truncf32u byte byte.169

Function i32truncf64s byte byte.170

Function i32truncf64u byte byte.171

Function i64extendi32s byte byte.172

Function i64extendi32u byte byte.173

Function i64truncf32s byte byte.174

Function i64truncf32u byte byte.175

Function i64truncf64s byte byte.176

Function i64truncf64u byte byte.177

Function f32converti32s byte byte.178

Function f32converti32u byte byte.179

Function f32converti64s byte byte.180

Function f32converti64u byte byte.181

Function f32demotef64 byte byte.182

Function f64converti32s byte byte.183

Function f64converti32u byte byte.184

Function f64converti64s byte byte.185

Function f64converti64u byte byte.186

Function f64promotef32 byte byte.187

Function i32reinterpretf32 byte byte.188

Function i64reinterpretf64 byte byte.189

Function f32reinterpreti32 byte byte.190

Function f64reinterpreti64 byte byte.191

Function i32extend8s byte byte.192

Function i32extend16s byte byte.193

Function i64extend8s byte byte.194

Function i64extend16s byte byte.195

Function i64extend32s byte byte.196

Function decodeop(code:byte) seq.word
let discard = 
 [unreachable, block, loop, END, br
  , brif, return, call, callindirect, drop
  , select, localget, localset, localtee, globalget
  , globalset, i32load, i64load, f32load, f64load
  , i32load8s, i32load8u, i32load16s, i32load16u, i64load8s
  , i64load8u, i64load16s, i64load16u, i64load32s, i64load32u
  , i32store, i64store, f32store, f64store, i32store8
  , i32store16, i64store8, i64store16, i64store32, memorysize
  , memorygrow, i32const, i64const, f32const, f64const
  , i32eqz, i32eq, i32ne, i32lts, i32ltu
  , i32gts, i32gtu, i32les, i32leu, i32ges
  , i32geu, i64eqz, i64eq, i64ne, i64lts
  , i64ltu, i64gts, i64gtu, i64les, i64leu
  , i64ges, i64geu, f32eq, f32ne, f32lt
  , f32gt, f32le, f32ge, f64eq, f64ne
  , f64lt, f64gt, f64le, f64ge, i32clz
  , i32ctz, i32popcnt, i32add, i32sub, i32mul
  , i32divs, i32divu, i32rems, i32remu, i32and
  , i32or, i32xor, i32shl, i32shrs, i32shru
  , i32rotl, i32rotr, i64clz, i64ctz, i64popcnt
  , i64add, i64sub, i64mul, i64divs, i64divu
  , i64rems, i64remu, i64and, i64or, i64xor
  , i64shl, i64shrs, i64shru, i64rotl, i64rotr
  , f32abs, f32neg, f32ceil, f32floor, f32trunc
  , f32nearest, f32sqrt, f32add, f32sub, f32mul
  , f32div, f32min, f32max, f32copysign, f64abs
  , f64neg, f64ceil, f64floor, f64trunc, f64nearest
  , f64sqrt, f64add, f64sub, f64mul, f64div
  , f64min, f64max, f64copysign, i32wrapi64, i32truncf32s
  , i32truncf32u, i32truncf64s, i32truncf64u, i64extendi32s, i64extendi32u
  , i64truncf32s, i64truncf32u, i64truncf64s, i64truncf64u, f32converti32s
  , f32converti32u, f32converti64s, f32converti64u, f32demotef64, f64converti32s
  , f64converti32u, f64converti64s, f64converti64u, f64promotef32, i32reinterpretf32
  , i64reinterpretf64, f32reinterpreti32, f64reinterpreti64, i32extend8s, i32extend16s
  , i64extend8s, i64extend16s, i64extend32s]
let i = toint.code,
if between(i + 1, 1, 197) then
 let r = 
  [
   "unreachable ? block loop ? ? ? ? ? ? ? END br brif ? return call callindirect ? ? ? ? ? ? ? ? drop select
    ? ? ? ? localget localset localtee globalget globalset ? ? ? i32load i64load f32load f64load i32load8s
    i32load8u i32load16s i32load16u i64load8s i64load8u i64load16s i64load16u i64load32s i64load32u i32store
    i64store f32store f64store i32store8 i32store16 i64store8 i64store16 i64store32 memorysize memorygrow
    i32const i64const f32const f64const i32eqz i32eq i32ne i32lts i32ltu i32gts i32gtu i32les i32leu i32ges
    i32geu i64eqz i64eq i64ne i64lts i64ltu i64gts i64gtu i64les i64leu i64ges i64geu f32eq f32ne f32lt f32gt
    f32le f32ge f64eq f64ne f64lt f64gt f64le f64ge i32clz i32ctz i32popcnt i32add i32sub i32mul i32divs
    i32divu i32rems i32remu i32and i32or i32xor i32shl i32shrs i32shru i32rotl i32rotr i64clz i64ctz i64popcnt
    i64add i64sub i64mul i64divs i64divu i64rems i64remu i64and i64or i64xor i64shl i64shrs i64shru i64rotl
    i64rotr f32abs f32neg f32ceil f32floor f32trunc f32nearest f32sqrt f32add f32sub f32mul f32div f32min
    f32max f32copysign f64abs f64neg f64ceil f64floor f64trunc f64nearest f64sqrt f64add f64sub f64mul f64div
    f64min f64max f64copysign i32wrapi64 i32truncf32s i32truncf32u i32truncf64s i32truncf64u i64extendi32s
    i64extendi32u i64truncf32s i64truncf32u i64truncf64s i64truncf64u f32converti32s f32converti32u f32converti64s
    f32converti64u f32demotef64 f64converti32s f64converti32u f64converti64s f64converti64u f64promotef32
    i32reinterpretf32 i64reinterpretf64 f32reinterpreti32 f64reinterpreti64 i32extend8s i32extend16s i64extend8s
    i64extend16s i64extend32s"
   _(i + 1)]
 ,
 if r ≠ "?" then r else "byte." + toword.i
else
 "byte." + toword.i 