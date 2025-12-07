Module token

use standard

use bits

use kernal

type token is value:bits

Function %(t:token) seq.word "Tok:([toword.t])"

function token(w:word, b:int) token token(tobits.b << 32 ∨ tobits.rawvalue.w)

function token(w:seq.word, b:int) token token(w sub 1, b)

Function toword(t:token) word word.toint(value.t ∧ mask.32)

Function towords(s:seq.token) seq.word
for acc = "", e ∈ s do acc + toword.e,
acc

function eqvclass(t:token) int toint(value.t >> 32)

type tkn is w:word, token:token

use encoding.tkn

function =(a:tkn, b:tkn) boolean w.a = w.b

function hash(a:tkn) int hash.w.a

use encoding.tkn

Function addprec(str:seq.word, internal:boolean) seq.word
for precedence = 0, e ∈ str
do
 if e ∈ "for" then precedence
 else if e ∈ "precedence" then -1
 else if precedence < 0 then
  if e ∈ "1 3 4 5 6 7 20 30 31 32 33 34 35 36 37 11" then toint.e
  else
   let prec = opprec.e
   assert prec ∈ [1, 3, 4, 5, 6, 7] report ":(e)does not have a precedence",
   prec
 else
  assert eqvclass.token.decode.encode.tkn(e, token(e, precedence)) = precedence report
   ":(e)has already been given a different precedence: /br
   :(str)",
  precedence,
 ""

Function tknencoding seq.word
let str =
 "precedence 20 Function function precedence 1 sub sup precedence 3 for * / >> << mod ∩ ∪ \ precedence 4+-∈ ∉ precedence 5 = > < ≠ ≥ ≤ precedence 6 ∧ precedence 7 ∨ ⊻ precedence 11 $mergecode precedence 30, precedence 31.precedence 32:"
 + "precedence 33(precedence 34)precedence 35[precedence 36]precedence 37"
 + dq sub 1,
addprec(str + "precedence+for ∈ ∉", true)

Function opprec(a:word) int
let k = findencode.tkn(a, token(a, 0)),
if isempty.k then 0 else eqvclass.token.k sub 1

use seq1.tkn

function %(a:tkn) seq.word ":(w.a):(toword.token.a):(eqvclass.token.a)"

Function totoken(w:word) token
let z = findencode.tkn(w, token(w, 0)),
if isempty.z then token.tobits.rawvalue.w else token.z sub 1

Function =(a:token, b:token) boolean
if value.a = value.b then true
else if value.a >> 32 = 0x0 then false
else value.a >> 32 = value.b >> 32

Function totokens(s:seq.word) seq.token
for p2 = empty:seq.token, e ∈ s do p2 + totoken.e,
p2

use seq.token

Export type:token 
