Module groupparagraphs

use fileio

use standard

use seq.seq.int

use seq.seq.seq.word

function findparagraph(break:seq.word, a:seq.seq.word, i:int)int
 \\ find paragraph starting with a word in break and return its index \\
 if length.a_i > 0 ∧ a_i_1 ∈ break then i else 0

function addpair(a:seq.seq.int, newbeginning:int)seq.seq.int
 \\ a is a seq of seq of length 2. A new pair is added by this function. \\
 if newbeginning = 0 then a
 else if length.a = 0 then [ [ 1, newbeginning - 1]]
 else
  let oldend =(last.a)_2
   a + [ [ oldend + 1, newbeginning - 1]]

function finishpair(p:seq.seq.int, len:int)seq.seq.int
 subseq(p, 2, length.p) + [ [ p_(length.p)_2 + 1, len]]

function extractblock(a:seq.seq.word, p:seq.int)seq.seq.word subseq(a, p_1, p_2)

Function groupparagraphs(break:seq.word, a:seq.seq.word)seq.seq.seq.word
 \\ Looks for paragraphs beginning with a word in break and returns seq of subsequences of paragraphs making up each block. In does this by creating a sequence of pairs of integers. Each pair contains beginning and end of a subsequence making up the block. \\
 ((for(@e ∈ finishpair((for(@e ∈ arithseq(length.a, 1, 1), acc = empty:seq.seq.int)addpair(acc, findparagraph(break, a, @e))), length.a), acc = empty:seq.seq.seq.word)acc + extractblock(a, @e)))

Function findlibclause(a:seq.seq.word, i:int)seq.word
 assert i < length.a report"No Library clause found"
 let s = a_i
  if s_1 = "Library"_1 then s else findlibclause(a, i + 1)

Function getlibraryinfo(libname:seq.word)seq.seq.word
 let a = gettext.[ merge([ first.libname] + "/" + last.libname + ".ls")]
 let s = findlibclause(a, 1)
 let l = break(s,"uses exports", true)
  assert length.l = 3 ∧ l_2_1 = "uses"_1
  ∧ l_3_1 = "exports"_1 report"lib clause problem"
   [ \\ dependentlibs \\ l_2 << 1, \\ filelist \\ l_1 << 1, \\ exports \\ l_3 << 1]

Function getlibrarysrc(libname:seq.word)seq.seq.word
 let filelist =(getlibraryinfo.libname)_2
  {((for(@e ∈ filelist, acc = empty:seq.seq.word)acc + gettext.[ merge([ first.libname] + "/" + @e + ".ls")]))}

Function getlibraryinfo(libname:word)seq.seq.word getlibraryinfo.[ libname]

Function getlibrarysrc(libname:word)seq.seq.word getlibrarysrc.[ libname]