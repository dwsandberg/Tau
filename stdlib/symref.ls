Module symref

use standard

use libraryModule

use symbol

use encoding.symbol

use seq.encodingpair.symbol

use seq.symbol

Export toint(symbolref)int

Export symbolref(int)symbolref

Export type:symbolref

Function symbolref(sym:symbol)symbolref symbolref.valueofencoding.encode.sym

Function assignencoding(l:seq.encodingpair.symbol, symbol)int length.l + 1

Function decode(s:symbolref)symbol decode.to:encoding.symbol(toint.s)

Function symbolrefdecode seq.symbol for acc = empty:seq.symbol, p = encoding:seq.encodingpair.symbol do acc + data.p /for(acc) 