 

 enumexample /tag // enum /id /h1

Module enumexample

use bits

use standard

The function name genEnum is treated as magic by the transform command. It auto generates the code
to implement enumeration types. This example implements two enumeration types. In the first enumeration
type Each word in the value list is given a value starting with 0. 

In the first example The question mark is a place holder for
numbers that with not be include in the type.

The second example uses an existing data type byte. 

function genEnum seq.seq.word 
[
 "newType: numbers names: ? two0 two1 ? two2 ? ? ? two3"
 , "existingType: byte decodeName: twodecode valueName: Two0 1 Two1 2 Two2 4 Two3 0x08"
]

<<<< Below is auto generated code >>>>

type numbers is toint:int

Export toint(numbers) int

Export numbers(i:int) numbers

Export type:numbers

Function =(a:numbers, b:numbers) boolean toint.a = toint.b

Function two0 numbers numbers.1

Function two1 numbers numbers.2

Function two2 numbers numbers.4

Function two3 numbers numbers.8  

Function decode(code:numbers) seq.word
let discard = [two0, two1, two2, two3]
let i = toint.code,
if between(i + 1, 1, 9) then
 let r = ["? two0 two1 ? two2 ? ? ? two3"] sub (i+1),
 if r ≠ "?" then r else "numbers." + toword.i
else "numbers." + toword.i

Function Two0 byte tobyte.1

Function Two1 byte tobyte.2

Function Two2 byte tobyte.4

Function Two3 byte tobyte.8

Function twodecode(code:byte) seq.word
let discard = [Two0, Two1, Two2, Two3]
let i = toint.code,
if between(i + 1, 1, 9) then
 let r = ["? Two0 Two1 ? Two2 ? ? ? Two3" sub (i + 1)],
 if r ≠ "?" then r else "byte." + toword.i
else "byte." + toword.i 