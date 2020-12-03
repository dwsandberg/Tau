#!/usr/local/bin/tau ; use testencoding ; testencoding



Module testencoding

Testing encodings

use UTF8

use seq.boolean

use seq.seq.char

use seq.char

use checking

use process.int

use process.set.int

use set.int

use stdlib

use process.testdeep

use seq.testdeep

use seq.set.int

function deepcopy(a:testdeep) testdeep   result.process.identity.a

function deepcopy(a:set.int) set.int  result.process.identity.a


function deepcopy(a:int) int a

use encoding.testrecord

use process.seq.encodingpair.testrecord

use seq.encodingpair.testrecord

use seq.seq.testrecord

use seq.testrecord

use seq.seq.word

use seq.tree.seq.word

use tree.seq.word

Export +(i:int, b:int)int


function =(a:testrecord, b:testrecord)boolean key.a = key.b

Function print(a:testrecord)seq.word [ toword.key.a] + body.a

function hash(a:testrecord)int key.a

Export type:testrecord

Function assignencoding(length:int, data:testrecord)int(randomint.1)_1

function add(b:seq.word)int
 let d = encoding:seq.encodingpair.testrecord
 let x = encode.testrecord(length.d + 1, b)
  1

type testrecord is record key:int, body:seq.word

function body(x:encodingpair.testrecord)seq.word body.data.x

function list(a:seq.encodingpair.testrecord)seq.seq.word @(+, body, empty:seq.seq.word, a)

Function testencoding seq.word // must export this module so encoding type can be figured out //
let p = process.process1
 if aborted.p then"Failed encoding" + message.p
 else
  let s1 = list.result.p
  let z = @(+, add, 0, ["firstadd","secondadd"])
  let s2 = list.result.process.process1
  let s3 = list.encoding:seq.encodingpair.testrecord
   check([ 
    3 = deepcopy.3, asset.[ 3, 7, 9] = deepcopy.asset.[ 3, 7, 9], deepcopy.testdeep1 = testdeep1 , s1 = ["A1","B2","C3","D4","E5"], s2 = ["firstadd","secondadd"] + s1, s3 = s2 
   ]
   ,"encoding")
   

Function process1 seq.encodingpair.testrecord
let discard = @(+, add, 0, ["A1","B2","C3","D4","E5"])
 encoding:seq.encodingpair.testrecord

Function nextpower(i:int, base:int, start:int)int if i > start then nextpower(i, base, start * base)else start

type testdeep is record fld1:seq.word, fld2:tree.seq.word, fld3:seq.char

function testdeep1 testdeep testdeep("A BC DEF", tree("LIT 1", [ tree."PARAM 1"]), decodeword."TEST"_1)

function =(a:testdeep, b:testdeep)boolean
 fld1.a = fld1.b ∧ fld2.a = fld2.b ∧ fld3.a = fld3.b