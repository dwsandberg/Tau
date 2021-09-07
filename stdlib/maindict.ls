module maindict

use UTF8

use dataio

use fileio

use standard

use tausupport

use words

use seq.int

use set.word

use encoding.seq.char

use seq.seq.char

use ioseq.encodingpair.seq.char

use seq.encodingpair.seq.char

use set.encodingpair.seq.char

use process.seq.encodingpair.seq.char

Function iosize:encodingpair.seq.char int 3

function +(p:place, r:encodingpair.seq.char)place
 p + valueofencoding.code.r + tointseq.data.r + hash.r

Function writedict(tin:seq.encodingpair.seq.char)int
let have = asset.initialdict
let t = toseq(asset.tin \ have)
 if isempty.t then 0
 else
  let p = if isempty.have then place(empty:seq.int, 0, empty:seq.int)
  else
   let d = getfile:int("maindictionary.data") << 2
    place(d, length.d, empty:seq.int)
   createfile("maindictionary.data", [ 0, 0] + data(p + t) + [ length.data.p + 1, length.data.p])

/Function loaddict(file:fileresult)int if size.file >-1 then let data = data.file // deepcopy. // get2(data, length.data)@ +(0, primitiveadd.@e)else 0

function get2(data:seq.int, i:int)seq.encodingpair.seq.char
 { file is built by append new data to the end followed by two words. The first is the start of the new data and the second is the size of the data before the new data was appended. To read the file the appended segements are combined into one long sequence. }
 if data_i = 0 then getseq2:encodingpair.seq.char(data, i - 1)
 else get2(data, data_i) + getseq2:encodingpair.seq.char(data, i - 1)

function getrecord:encodingpair.seq.char(data:seq.int, i:int)encodingpair.seq.char
 encodingpair(to:encoding.seq.char(getint(data, i)), tocharseq.getintseq(data, i + 1))

module dataio

use UTF8

use real

use standard

function newplace place place(empty:seq.int, 0, empty:seq.int)

type place is this:seq.int, offset:int, data:seq.int

Export type:place

offset is offset to data

Export place(this:seq.int, offset:int, data:seq.int)place

Export this(place)seq.int

Export offset(place)int

Export data(place)seq.int

Function +(p:place, c:seq.int)place
 place(this.p + (next.p + 1), offset.p, data.p + [ 0, length.c] + c)

Function +(p:place, c:int)place place(this.p + c, offset.p, data.p)

Function +(p:place, c:real)place place(this.p + representation.c, offset.p, data.p)

Function +(p:place, w:word)place p + tointseq.decodeword.w

Function getword(data:seq.int, i:int)word encodeword.tocharseq.getintseq(data, data_i)

Function getrecord:word(data:seq.int, i:int)word let y = getintseq(data, i)
 encodeword.tocharseq.y

Function getintseq(data:seq.int, seqpointer:int)seq.int
let index = data_seqpointer
let len = data_(index + 1)
 subseq(data, index + 2, index + 2 + len - 1)

Function getint(data:seq.int, i:int)int data_i

Function getreal(data:seq.int, i:int)real casttoreal.data_i

Function next(p:place)int offset.p + length.data.p

module ioseq.T

use dataio

use standard

use process.T

use seq.T

type ioseq is sequence, data:seq.int, offset:int, k:seq.T

Export data(s:ioseq.T)seq.int

unbound getrecord:T(seq.int, int)T

unbound +(place, T)place

unbound iosize:T int

Function_(a:ioseq.T, i:int)T
let size = iosize:T
let index = offset.a + size * (i - 1) + 2
 assert between(i, 1,(data.a)_(offset.a + 1))report"out of bounds2"
 + for acc ="", @e = [ i, size, index] + data.a do acc + toword.@e /for(acc)
  getrecord:T(data.a, index)

Export offset(ioseq.T)int

Function getseq2:T(data:seq.int, seqpointer:int)seq.T
let offset = data_seqpointer
 toseq.ioseq(data_(offset + 1), data, offset, empty:seq.T)

Function +(p:place, s:seq.T)place
let size = iosize:T
let q = place([ 0, length.s], next.p + length.s * size + 2, empty:seq.int)
let r = for acc = q, @e = s do acc + @e /for(acc)
 place(this.p + (next.p + 1), offset.p, data.p + this.r + data.r)