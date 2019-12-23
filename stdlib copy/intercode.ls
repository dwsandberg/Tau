Module intercode

use persistant

use reconstruct

use stdlib

type intercode is record codes:seq.seq.int, coding:seq.inst, defines:seq.int

defines are indices into coding that indicate which functions are defined and indices into codes that give a seq of integers which are indices into coding

function intercode(seq.seq.int, seq.inst, seq.int)intercode export

function codes(intercode)seq.seq.int export

function coding(intercode)seq.inst export

function defines(intercode)seq.int export

type inst is record towords:seq.word, flags:seq.word, returntype:mytype

Function inst(towords:seq.word, flags:seq.word, returntype:mytype)inst export

Function mangledname(a:inst)word towords(a)_1

Function nopara(a:inst)int toint(towords(a)_2)

function flags(a:inst)seq.word export

function towords(a:inst)seq.word export

function returntype(a:inst)mytype export

function addwordseq(linklists2, seq.word)ipair.linklists2 export

Function worddata seq.int export

Function wordcount int export

Function addliblib(linklists2, liblib)ipair.linklists2 export

Function a(linklists2)seq.int export

Function initializer(conststypex:encoding.llvmtype, data:linklists2)int export

