module maindict

use UTF8

use encoding.seq.char

use ioseq.encodingrep.seq.char

use blockseq.seq.encodingrep.seq.char

use deepcopy.seq.encodingrep.seq.char

use seq.encodingrep.seq.char

use set.encodingrep.seq.char

use seq.seq.char

use dataio

use fileio

use stdlib

use set.word

use words

function ?(a:encodingrep.seq.char, b:encodingrep.seq.char)ordering valueofencoding.code.a ? valueofencoding.code.b

function +(p:place, r:encodingrep.seq.char)place
 p + valueofencoding.code.r + tointseq.data.r + hash.r

Function writedict(tin:seq.encodingrep.seq.char)int
 let have = asset.initialdict
 let t = toseq(asset.tin - have)
  if isempty.t then 0
  else
   let p = if isempty.have then place(empty:seq.int, 0, empty:seq.int)
   else
    let d = data.getfile2."maindictionary.data"
     place(d, length.d, empty:seq.int)
    createfile("maindictionary.data", [ 0, 0] + data(p + t) + [ length.data.p + 1, length.data.p])

Function loaddict(file:fileresult)int
 if size.file > -1 then
 let data = data.file
   add(wordencoding, deepcopy.get2(data, length.data))
 else 0

function get2(data:seq.int, i:int)seq.encodingrep.seq.char
 // file is built by append new data to the end followed by two words. The first is the start of the new data and the second is the size of the data before the new data was appended. To read the file the appended segements are combined into one long sequence. //
 if data_i = 0 then getseq2:encodingrep.seq.char(data, i - 1)
 else get2(data, data_i) + getseq2:encodingrep.seq.char(data, i - 1)

function getrecord:encodingrep.seq.char(data:seq.int, i:int)encodingrep.seq.char
 encodingrep(toencoding:seq.char(getint(data, i)), tocharseq.getintseq(data, i + 1), getint(data, i + 2))

Function initialdict seq.encodingrep.seq.char builtin.usemangle

module dataio

use UTF8

use real

use stdlib

function newplace place place(empty:seq.int, 0, empty:seq.int)

type place is record this:seq.int, offset:int, data:seq.int

Function type:place internaltype export

offset is offset to data

Function place(this:seq.int, offset:int, data:seq.int)place export

Function this(place)seq.int export

Function offset(place)int export

Function data(place)seq.int export

Function +(p:place, c:seq.int)place
 place(this.p + (next.p + 1), offset.p, data.p + [ 0, length.c] + c)

Function +(p:place, c:int)place place(this.p + c, offset.p, data.p)

Function +(p:place, c:real)place place(this.p + representation.c, offset.p, data.p)

Function +(p:place, w:word)place p + tointseq.decodeword.w

Function getword(data:seq.int, i:int)word encodeword.tocharseq.getintseq(data, data_i)

Function getrecord:word(data:seq.int, i:int)word
 // assert false report"JKLword"+ @(+, toword,"", [ i]+ data)//
 let y = getintseq(data, i)
  // assert false report"JKLword"+ @(+, toword,"", [ i]+ data)+ @(+, toword,":", y)+ encodeword.y //
  encodeword.tocharseq.y

Function getintseq(data:seq.int, seqpointer:int)seq.int
 let index = data_seqpointer
 let len = data_(index + 1)
  subseq(data, index + 2, index + 2 + len - 1)

Function getint(data:seq.int, i:int)int data_i

Function getreal(data:seq.int, i:int)real casttoreal.data_i

Function next(p:place)int offset.p + length.data.p

module ioseq.T

use deepcopy.T

use seq.T

use dataio

use stdlib

type ioseq is sequence length:int, data:seq.int, offset:int, k:seq.T

Function data(s:ioseq.T)seq.int export

Function length(s:ioseq.T)int export

Function getrecord:T(seq.int, int)T unbound

Function +(place, T)place unbound

Function_(a:ioseq.T, i:int)T
 let size = sizeoftype:T
 let index = offset.a + size * (i - 1) + 2
  // assert false report"JKLL"+ @(+, toword,"", [ i, size, index]+ data.a)//
  assert between(i, 1,(data.a)_(offset.a + 1))report"out of bounds2" + @(+, toword,"", [ i, size, index] + data.a)
   getrecord:T(data.a, index)

Function offset(ioseq.T)int export

Function getseq2:T(data:seq.int, seqpointer:int)seq.T
 let offset = data_seqpointer
  toseq.ioseq(data_(offset + 1), data, offset, empty:seq.T)

Function +(p:place, s:seq.T)place
 let size = sizeoftype:T
 let q = place([ 0, length.s], next.p + length.s * size + 2, empty:seq.int)
 let r = @(+, identity, q, s)
  place(this.p + (next.p + 1), offset.p, data.p + this.r + data.r)