Module symboldict

use seq.commoninfo

use set.mytype

use standard

use symbol

use seq.symbol

use set.symbol

use set.symdef

Export type:commoninfo

Export types(commoninfo)set.mytype

Export modname(commoninfo)modref

Export lib(commoninfo)word

Export mode(commoninfo)word

Export input(commoninfo)seq.word

Export commoninfo(input:seq.word, modname:modref, lib:word, types:set.mytype, mode:word)commoninfo

type commoninfo is input:seq.word, modname:modref, lib:word, types:set.mytype, mode:word

Function lookupbysig(dict:symboldict, sym:symbol)set.symbol findelement2(asset.dict, sym)

type symboldict is asset:set.symbol, requires:set.symdef, commonX:seq.commoninfo

Export symboldict(asset:set.symbol, requires:set.symdef, commonX:seq.commoninfo)symboldict

Export type:symboldict

Export asset(symboldict)set.symbol

Function symboldict(d:set.symbol, common:seq.commoninfo)symboldict symboldict(d, empty:set.symdef, common)

Function common(d:symboldict)commoninfo first.commonX.d

Function requires(d:symboldict, sym:symbol)seq.symbol
if hasrequires.sym then
 let t = getSymdef(requires.d, sym)
 if isempty.t then empty:seq.symbol
 else
  assert not.isempty.t report"requires" + print.sym
  code.t_1
else empty:seq.symbol

Function empty:symboldict symboldict symboldict(empty:set.symbol, empty:set.symdef, empty:seq.commoninfo)

Function +(d:symboldict, sym:symbol)symboldict symboldict(asset.d + sym, requires.d, commonX.d)

Function -(d:symboldict, s:set.symbol)symboldict symboldict(asset.d \ s, requires.d, commonX.d)

Function ∪(d:symboldict, s:set.symbol)symboldict symboldict(asset.d ∪ s, requires.d, commonX.d)

Function cardinality(d:symboldict)int cardinality.asset.d

Export type:bindinfo

type bindinfo is dict:symboldict, code:seq.symbol, types:seq.mytype, tokentext:seq.word

Export dict(bindinfo)symboldict

Export code(bindinfo)seq.symbol

Export types(bindinfo)seq.mytype

Export tokentext(bindinfo)seq.word

Export bindinfo(dict:symboldict, code:seq.symbol, types:seq.mytype, tokentext:seq.word)bindinfo 