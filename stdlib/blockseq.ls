Module blockseq(T)

use packedseq.T

use packedseq.seq.T

use seq.T

use seq.seq.T

use stdlib

/use internals.T

type blockseq is sequence length:int, blocksize:int, data:seq.seq.T

Function deepcopy(T)T builtin.DEEPCOPY

Function blockit(s:seq.T)seq.T 
 let blocksize = 10000 / sizeoftype:T 
  if length.s ≤ blocksize 
  then packed.s 
  else newblockseq(length.s, @(+, subblock(s, blocksize), empty:seq.seq.T, arithseq((length.s + blocksize - 1)/ blocksize, blocksize, 1)))

function newblockseq(length:int, s:seq.seq.T)seq.T toseq.blockseq(length, length(s_1), packed.s)

function subblock(s:seq.T, blocksize:int, i:int)seq.T packed.subseq(s, i, i + blocksize - 1)

function_(a:blockseq.T, i:int)T data(a)_((i - 1)/ blocksize.a + 1)_((i - 1)mod blocksize.a + 1)

/Function pstruct2(a:seq.T)seq.word iftype x:pseq.T = a then"["+ toword.length.x + pstruct2.a.x +"/"+ pstruct2.b.x +"]"else iftype y:blockseq.T = a then"("+ toword.length.y + toword.blocksize.y + toword.length.data.y +")"else"^"+ toword.length.a

Function simplepackedbyte(a:seq.T)seq.T builtin.usemangle

let lengthword =(length.a + 7)/ 8 let b = allocatespace(lengthword + 2)// set the first fields to indicate packedbytes and length // let discard2 = setfld3(address.b, 1, 0)let discard3 = setfld3(address.b, length.a, 1)// zero last word allocated for overrun // let discard4 = setfld3(address.b, 0, lengthword + 1)// set the flds of seq // let discard = @(+, setbyte(b, a), 0, arithseq(length.a, 1, 1))b

Function packedbyte(s:seq.T)seq.T 
 let blocksize = 80000 
  if length.s ≤ blocksize 
  then simplepackedbyte.s 
  else newblockseq(length.s, @(+, subblockbyte(s, blocksize), empty:seq.seq.T, arithseq((length.s + blocksize - 1)/ blocksize, blocksize, 1)))

function subblockbyte(s:seq.T, blocksize:int, i:int)seq.T simplepackedbyte.subseq(s, i, i + blocksize - 1)

function topackedseq(s:seq.T)packedseq.T builtin.FROMSEQ

Function ispackedseq(s:seq.T)boolean not(length.topackedseq.s = 0)

function toblockseq(s:seq.T)blockseq.T builtin.FROMSEQ

Function isblockseq(s:seq.T)boolean not(length.toblockseq.s = 0)

