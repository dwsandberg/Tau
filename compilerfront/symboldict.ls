Module symboldict

use seq1.mytype

use seq.mytype

use standard

use seq1.symbol

use set.symbol

use symbol1

use set.symdef

Export type:symboldict

Export asset(symboldict) set.symbol

Export symboldict(asset:set.symbol, requires:set.symdef) symboldict

Function lookupbysig(dict:symboldict, sym:symbol) set.symbol findelement2(asset.dict, sym)

Function lookupbysig(dict:symboldict, name:seq.word) set.symbol
lookupbysig(dict, symbol(internalmod, name, empty:seq.mytype, typeint))

type symboldict is asset:set.symbol, requires:set.symdef

Function symboldict(d:set.symbol) symboldict symboldict(d, empty:set.symdef)

Function requires(d:symboldict, sym:symbol) seq.symbol
if hasrequires.sym then
 let t = getSymdef(requires.d, sym),
 if isempty.t then empty:seq.symbol
 else
  assert not.isempty.t report "requires:(sym)",
  code.t sub 1
else empty:seq.symbol

Function restorenext(dict:symboldict) symboldict
let thisnesting = lookupbysig(dict, "for") sub 1
let b = getCode(requires.dict, thisnesting)
let dict1 =
 if n.b = 2 then dict - asset(b + thisnesting)
 else dict - asset(subseq(b, 1, 2) + thisnesting) + b sub 3 + b sub 4,
dict1
 + placeholder(".fora", resulttype.thisnesting)
 + placeholder(".forb", resulttype.thisnesting)
 + placeholder(".forc", resulttype.thisnesting)

function placeholder(name:seq.word, basetype:mytype) symbol
symbol(
 moduleref("internallib $for", basetype)
 , [merge.".:(name)"]
 , empty:seq.mytype
 , basetype
)

Function addAccum(
dict:symboldict
, nextSym:symbol
, basetype:mytype
, oldnesting:set.symbol
, elementSym:symbol
) symboldict
let nestingsym = symbol(moduleref("internallib $for", basetype), "for", empty:seq.mytype, basetype)
let tmp =
 if isempty.oldnesting then [nextSym, elementSym]
 else [nextSym, elementSym, oldnesting sub 1, getCode(requires.dict, oldnesting sub 1) sub 1]
let a = asset.dict
for acc = a \ asset(tmp << 2), n ∈ [".forxx", ".foryy"]
while n.acc < n.a
do acc + placeholder(n, basetype),
symboldict(acc + nextSym + nestingsym, requires.dict + symdef(nestingsym, tmp, 0))

Function empty:symboldict symboldict symboldict(empty:set.symbol, empty:set.symdef)

Function +(d:symboldict, sym:symbol) symboldict symboldict(asset.d + sym, requires.d)

Function -(d:symboldict, s:set.symbol) symboldict symboldict(asset.d \ s, requires.d)

Function ∪(d:symboldict, s:set.symbol) symboldict symboldict(asset.d ∪ s, requires.d)

Function cardinality(d:symboldict) int n.asset.d 
