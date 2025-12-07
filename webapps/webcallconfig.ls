Module webcallconfig

use file

use standard

use compilerfrontT.callconfig

use symbol1

Export compilerFront:callconfig(seq.word, seq.file, seq.word, seq.word) midpoint

Export type:callconfig

type callconfig is a:int

Function callfunc:callconfig(ctsym:symbol, typedict:typedict, stk:seq.int) seq.int
if ctsym = symbol(internalmod, "+", [typeint, typeint], typeint) then [stk sub 1 + stk sub 2]
else if ctsym = symbol(internalmod, "*", [typeint, typeint], typeint) then [stk sub 1 * stk sub 2]
else if ctsym = symbol(internalmod, "-", [typeint, typeint], typeint) then [stk sub 1 - stk sub 2]
else if ctsym = symbol(internalmod, "/", [typeint, typeint], typeint) then [stk sub 1 / stk sub 2]
else if ctsym = symbol(internalmod, "=", [typeint, typeint], typeboolean)
∨ ctsym = symbol(internalmod, "=", [typeboolean, typeboolean], typeboolean) then [if stk sub 1 = stk sub 2 then 1 else 0]
else empty:seq.int
