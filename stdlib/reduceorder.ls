
#!/usr/local/bin/tau ; use reduceorder; parse("function a ( a:seq.int,b:int ) int 23+23")

Module reduceorder

use parsersupport.seq.int

use encoding.seq.token.seq.int

use seq.seq.token.seq.int

use seq.token.seq.int

use format

use seq.int

use seq.seq.mytype

use seq.mytype

use stdlib

use seq.seq.symbol

use seq.symbol

use set.symbol

use symbol

use set.word


function errormessage(message:seq.word, input:seq.word, place:int)seq.word message + prettynoparse.subseq(input, 1, place)

 

Function reduceorder(input:seq.word) seq.int
 // let a = if length.cachevalue = 0 then let discard = encode(sortedlextable:bindinfo){data.(cachevalue)_1 } else data.(cachevalue)_1 //
 let a = sortedlextable:seq.int
  // assert isempty.dict.b report @(+, print,"", toseq.dict.b)+ stacktrace //
   parse:seq.int(empty:seq.int, a, input)
 
function forward(stk:seq.int, token:seq.int)seq.int  stk

function attribute:seq.int(w:seq.word) seq.int empty:seq.int

function text(b:seq.int)seq.word "?" 

function hash(l:seq.token.seq.int)int length.l

function assignencoding(l:int, a:seq.token.seq.int)int assignrandom(l, a)



Function action(ruleno:int, input:seq.token.seq.int, R:reduction.seq.int)seq.int
if ruleno = // G F # // 1 then  R_1 + 1 else 
if ruleno = // F W NM(FP)T E // 2 then R_7 + 2  else
if ruleno = // F W N(FP)T E // 3 then R_7 +  3 else
if ruleno = // F W NM T E // 4 then R_4 + 4 else 
if ruleno = // F W NM is W P // 5 then R_5 + 5 else
if ruleno = // F T // 6 then R_1 + 6 else 
if ruleno = // FP P // 7 then R_1 +7 else 
if ruleno = // P T // 8 then R_1 +8 else 
if ruleno = // P P, T // 9 then R_3 +9 else 
if ruleno = // P W:T // 10 then R_3 +10 else 
if ruleno = // P P, W:T // 11 then R_5 +11 else 
if ruleno = // P comment W:T // 12 then R_3 +12 else 
if ruleno = // P P, comment W:T // 13 then R_5 +13 else 
if ruleno = // E NM // 14 then R_1 +14 else 
if ruleno = // E NM(L)// 15 then R_4 +15 else 
if ruleno = // E(E)// 16 then R_2+16 else 
if ruleno = // E { E } // 17 then R_2 else 
if ruleno = // E if E then E else E // 18 then R_6 + 18 else 
if ruleno = // E unused // 19 then   R_1 + 19 else  
if ruleno = // E E_E // 20 then  R_3 + 20 else 
if ruleno = // E-E // 21 then  R_2 + 21 else 
if ruleno = // E W.E // 22 then  R_3 + 22 else 
if ruleno = // E E * E // 23 then  R_3 + 23 else 
if ruleno = // E E-E // 24 then  R_3 + 24 else  
if ruleno = // E E = E // 25 then  R_3 + 25 else 
if ruleno = // E E > E // 26 then R_3 + 26 else 
if ruleno = // E E ∧ E // 27 then  R_3 + 27 else  
if ruleno = // E E ∨ E // 28 then  R_3 + 28 else  
if ruleno = // L E // 29 then  R_1 + 29 else 
if ruleno = // L L, E // 30 then  R_3 + 30 else  
if ruleno = // E [ L]// 31 then  R_3 + 31 else 
if ruleno = // A let W = E // 32 then  R_4 +32 else 
if ruleno = // E A E // 33 then  R_2 +33 else 
if ruleno = // E assert E report E E // 34 then  R_5 +34 else 
if ruleno = // E I // 35 then  R_1 +35 else  
if ruleno = // E I.I // 36 then  R_3 +36 else 
if ruleno = // T W // 37 then  R_1 +37 else 
if ruleno = // T W.T // 38 then  R_3 +38 else  
if ruleno = // E $wordlist // 39 then  R_1 +39 else 
if ruleno = // E comment E // 40 then R_2+40 else 
if ruleno = // N_// 41 then R_1+41 else 
if ruleno = // N-// 42 then R_1+42 else 
if ruleno = // N = // 43 then R_1+43 else 
if ruleno = // N > // 44 then R_1+44 else 
if ruleno = // N * // 45 then R_1+45 else 
if ruleno = // N ∧ // 46 then R_1+46 else 
if ruleno = // N ∨ // 47 then R_1+47 else 
if ruleno = // K W.E // 48 then  R_3 +48 else 
if ruleno = // K N.E // 49 then  R_3 +49 else  
if ruleno = // K N // 50 then R_1+50 else 
if ruleno = // K NM(L)// 51 then  R_4 +51 else 
if ruleno = // K NM // 52 then R_1+52 else 
if ruleno = // NM W // 53 then R_1+53 else 
if ruleno = // NM W:T // 54 then  R_3 +54 else 
if ruleno = // E @(K, K, E, E)// 55 then R_9+54 else
if ruleno = // D E @@ // 56 then  R_1 +56 else 
if ruleno = // E D NM(E, L)// 57 then  R_1 +57 else  
assert ruleno = // E D N(E, L)// 58 report"invalid rule number"+ toword.ruleno 
 R_1 +58  

