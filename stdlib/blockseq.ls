Module blockseq.T

use packedseq.T

use packedseq.seq.T

use unsafe.T

use seq.T

use seq.seq.T

use stdlib

Function packed(seq.T)seq.T export

Function type:seq.T internaltype export

type blockseq is sequence length:int, blocksize:int, data:seq.seq.T

Function blockit(s:seq.T)seq.T
 let blocksize = 10000 / sizeoftype:T
  if length.s ≤ blocksize then packed.s
  else
   newblockseq(length.s
   , @(+, subblock(s, blocksize), empty:seq.seq.T, arithseq((length.s + blocksize - 1) / blocksize, blocksize, 1)))

function newblockseq(length:int, s:seq.seq.T)seq.T toseq.blockseq(length, length.s_1, packed.s)

function subblock(s:seq.T, blocksize:int, i:int)seq.T packed.subseq(s, i, i + blocksize - 1)

Function_(a:blockseq.T, i:int)T
 (data.a)_((i - 1) / blocksize.a + 1)
 _((i - 1) mod blocksize.a + 1)

/Function pstruct2(a:seq.T)seq.word iftype x:pseq.T = a then"["+ toword.length.x + pstruct2.a.x +"/"+ pstruct2.b.x +"]"else iftype y:blockseq.T = a then"("+ toword.length.y + toword.blocksize.y + toword.length.data.y +")"else"^"+ toword.length.a

/function topackedseq(s:seq.T)packedseq.T builtin.FROMSEQ

/Function ispackedseq(s:seq.T)boolean(length.topackedseq.s &ne 0)

/function toblockseq(s:seq.T)blockseq.T builtin.FROMSEQ

/Function isblockseq(s:seq.T)boolean(length.toblockseq.s &ne 0)