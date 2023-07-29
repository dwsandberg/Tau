Module webIO

use SpecialImports

use UTF8

use bits

use format

use real

use standard

use textio

use webIOtypes

Export type:jsbytes

Export towords(a:jsbytes) seq.word

Export setElementValue(id:seq.word, text:seq.word) int

Export getattributes(id:seq.word, attributes:seq.word) seq.word

Export setAttribute(id:seq.word, att:seq.word, value:seq.word) real

Export replaceSVG(name:seq.word, xml0:seq.word) real

Export getElementValue(id:seq.word) seq.word

Export getElementValue:jsbytes(id:seq.word) jsbytes

Export jsUTF8(t:seq.byte) jsbytes

Export callevent(id:seq.word, event:seq.word) int

Function setElementValue(id:seq.word, text:jsbytes) int
{OPTION NOINLINE}
intpart.setelementvalue(token.id, text)

Function setElementValue(id:seq.word, text:seq.word) int
{OPTION NOINLINE}
intpart.setelementvalue(token.id, jsUTF8.toseqbyte.HTMLformat.text)

Function getElementValue(id:seq.word) seq.word towords.getelementvalue.token.id

Function getElementValue:jsbytes(id:seq.word) jsbytes getelementvalue.token.id

Function getattributes(id:seq.word, attributes:seq.word) seq.word
towords.getattributes2(token.id, jsUTF8.toseqbyte.HTMLformat.attributes)

Function getLines(id:seq.word) seq.seq.word
let a = toseqbyte.getattributes2(token.id, jsUTF8.toseqbyte.HTMLformat."textContent")
for acc = empty:seq.seq.word, l ∈ breaklines.a do acc + towords.l,
acc

Function setAttribute(id:seq.word, att:seq.word, value:seq.word) real
setattribute2(token.id, token.att, jsUTF8.toseqbyte.HTMLformat.value)

Function callevent(id:seq.word, event:seq.word) int
{OPTION NOINLINE}
intpart.callevent2(token.id, token.event)

Function replaceSVG(name:seq.word, xml0:seq.word) real
let none = 1_"N"
let xml =
 for xml = "", hasquote = none, w ∈ xml0
 do
  if w ∈ dq then
  if hasquote = none then next(xml + w + "/nosp", w) else next(xml + w, none)
  else if w = 1_"/br" then
  next(xml + encodeword.[char.10], hasquote)
  else next(xml + w, hasquote)
 ,
 xml
,
replacesvg(token.name, jsUTF8.toseqbyte.toUTF8.xml) 