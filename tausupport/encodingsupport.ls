Module encodingsupport

use bitcast.einfo

use seq1.einfo

use bitcast.seq.einfo

use bitcast.evector

use bitcast.int

use kernal

use indirect.processflds

use seq.processflds

use ptr

use bitcast.ptr

use encoding.typename

use bitcast.encodingstate.typename

use word

use seq.word

Export type:einfo

Export type:processflds

Export type:typename

type typename is name:seq.word

Function geteinfo(gl:ptr, name:seq.word) einfo
let no = fld:int(gl, 0)
let encodingno =
 if no > 0 then no
 else if {subseq(name, 1, 2)="char kernal"}subseq(name, 1, 1) = "char" then 1
 else if subseq(name, 1, 2) = "typename encodingsupport" then 2
 else
  let newno = addorder.typename.name + 2
  let discard = set(gl, newno),
  newno,
geteinfo2(encodingno, 0)

Function geteinfo2(encodingno:int, dummy:int) einfo
let cp = currentprocess
let a = evector.cp,
if encodingno = encodingno.thisone.a then thisone.a
else if encodingno ≤ n.vector.a ∧ encodingno.(vector.a) sub encodingno > 0 then
 let this = (vector.a) sub encodingno
 let discard = set(set(toptr.a, toptr.vector.a), toptr.this),
 this
else evectorUpdate.einfo(empty:encodingstate.typename, encodingno, cp)

Function evectorUpdate(b:ptr) ptr toptr.evectorUpdate.bitcast:einfo(b)

Function evectorUpdate(b:einfo) einfo
let cp = currentprocess
let a = evector.cp
let encodingno = encodingno.b
let vin = vector.a
let newlen = max(encodingno, n.vin)
let t = allocatespace(newlen + 2)
let newvector = bitcast:seq.einfo(t)
let discard =
 for
  acc = set(set(t, 0), newlen)
  , cnt = 1
  , e ∈ vin + constantseq(encodingno - n.vin, einfo(empty:encodingstate.typename, 0, cp))
 do next(set(acc, toptr(if cnt = encodingno then b else e)), cnt + 1),
 0
let discard2 = set(set(toptr.a, toptr.newvector), toptr.b),
b

function =(a:typename, b:typename) boolean name.a = name.b

function hash(a:typename) int hash.name.a

type processflds is
aborted:boolean
, message:int
, messageUTF8:int
, body:int
, body2:int
, evector:evector
, parentprocess:ptr

builtin currentprocess processflds

type einfo is state45:ptr, encodingno:int, allocatein:indirect.processflds

type evector is vector:seq.einfo, thisone:einfo

function einfo(
state45:encodingstate.typename
, encodingno:int
, allocatein:processflds
) einfo
einfo(toptr.state45, encodingno, indirect.allocatein) 