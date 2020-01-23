Module intercode

use persistant

use stdlib

type intercode is record codes:seq.seq.int, coding:seq.inst, defines:seq.int

Defines are ipointers into coding that indicate which functions are defined.

The field index of inst is a pointer into codes

Codes give a seq of integers which are indices into coding

function intercode(seq.seq.int, seq.inst, seq.int)intercode export

function codes(intercode)seq.seq.int export

function coding(intercode)seq.inst export

function defines(intercode)seq.int export

Function type:inst internaltype export

Function type:intercode internaltype export


type inst is record towords:seq.word, flags:seq.word, returntype:mytype, index:int

Function inst(towords:seq.word, flags:seq.word, returntype:mytype)inst inst(towords, flags, returntype, 0)

Function addindex(a:inst, i:int)inst inst(towords.a, flags.a, returntype.a, i)

Function mangledname(a:inst)word towords(a)_1

Function nopara(a:inst)int toint(towords(a)_2)

function flags(a:inst)seq.word export

function towords(a:inst)seq.word export

function returntype(a:inst)mytype export

function index(a:inst)int export

function addwordseq(linklists2, seq.word)ipair.linklists2 export


Function wordcount int export

Function addliblib(linklists2, liblib)ipair.linklists2 export

Function a(linklists2)seq.int export

Function addwordseq(t:linklists2, a:seq.word)ipair.linklists2 export

Function addconst(l:linklists2, fullinst:seq.word)ipair.linklists2 export

Function registerword(a:word)int export

Function createlinkedlists linklists2 export

Function initializer(conststypex:llvmtype, data:linklists2)int export

use textio

use seq.inst

use seq.seq.int

Function print(c:intercode,i:inst) seq.word
      towords.i+     @(+, towords2, ""  ,       @(+,_.coding.c,empty:seq.inst, (codes.c)_index.i))

function   towords2(i:inst) seq.word if (towords.i)_1 in "PARAM LIT" then [(towords.i)_1]+towords.decodeword.(towords.i)_2 else towords.i


