

module webIO

use inputoutput

use standard

use  bits

use seq.byte

Export type:jsbytes

Export towords(a:jsbytes)seq.word

Export setElementValue(id:seq.word, text:seq.word)int

Export getattributes(id:seq.word, attributes:seq.word)seq.word

Export setAttribute(id:seq.word, att:seq.word, value:seq.word)real

Export replaceSVG(name:seq.word, xml0:seq.word)real

Export setElementValue(id:seq.word, text:seq.word)int

Export getElementValue(id:seq.word)seq.word

Export setElementValue(id:seq.word, text:jsbytes)int

Export getElementValue:jsbytes(id:seq.word)jsbytes

Export jsUTF8(t:seq.byte)jsbytes
