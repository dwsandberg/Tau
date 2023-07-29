Module symboldict

use otherseq.mytype

use seq.mytype

use standard

use symbol

use otherseq.symbol

use set.symbol

use set.symdef

Export type:symboldict

Export asset(symboldict) set.symbol

Export symboldict(asset:set.symbol, requires:set.symdef) symboldict

Function lookupbysig(dict:symboldict, sym:symbol) set.symbol findelement2(asset.dict, sym)

Function lookupbysig(dict:symboldict, name:seq.word) set.symbol
lookupbysig(dict, symbol(internalmod, name, typeint))

type symboldict is asset:set.symbol, requires:set.symdef

Function symboldict(d:set.symbol) symboldict symboldict(d, empty:set.symdef)

Function requires(d:symboldict, sym:symbol) seq.symbol
if hasrequires.sym then
 let t = getSymdef(requires.d, sym),
  if isempty.t then
  empty:seq.symbol
  else assert not.isempty.t report "requires^(sym)", code.1_t
else empty:seq.symbol

Function restorenext(dict:symboldict) symboldict
let thisnesting = 1_lookupbysig(dict, "for")
let b = getCode(requires.dict, thisnesting)
let dict1 =
 if n.b = 2 then
 dict - asset(b + thisnesting)
 else dict - asset(subseq(b, 1, 2) + thisnesting) + 3_b + 4_b
,
dict1
 + placeholder(".fora", resulttype.thisnesting)
 + placeholder(".forb", resulttype.thisnesting)
 + placeholder(".forc", resulttype.thisnesting)

function placeholder(name:seq.word, basetype:mytype) symbol
symbol(moduleref("internallib $for", basetype), [merge.".^(name)"], empty:seq.mytype, basetype)

Function addAccum(
 dict:symboldict
 , nextSym:symbol
 , basetype:mytype
 , oldnesting:set.symbol
 , elementSym:symbol
) symboldict
let nestingsym = symbol(moduleref("internallib $for", basetype), "for", empty:seq.mytype, basetype)
let tmp =
 if isempty.oldnesting then
 [nextSym, elementSym]
 else [nextSym, elementSym, 1_oldnesting, 1_getCode(requires.dict, 1_oldnesting)]
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