Module groupparagraphs

use fileio

use seq.seq.int

use stdlib

use seq.seq.seq.word

function findparagraph(break:seq.word, a:seq.seq.word, i:int)int
 // find paragraph starting with a word in break and return its index //
 if length.a_i > 0 ∧ a_i_1 in break then i else 0

function addpair(a:seq.seq.int, newbeginning:int)seq.seq.int
 // a is a seq of seq of length 2. A new pair is added by this function. //
 if newbeginning = 0 then a
 else if length.a = 0 then [ [ 1, newbeginning - 1]]
 else
  let oldend =(last.a)_2
   a + [ [ oldend + 1, newbeginning - 1]]

function finishpair(p:seq.seq.int, len:int)seq.seq.int
 subseq(p, 2, length.p) + [ [ p_(length.p)_2 + 1, len]]

function extractblock(a:seq.seq.word, p:seq.int)seq.seq.word subseq(a, p_1, p_2)

Function groupparagraphs(break:seq.word, a:seq.seq.word)seq.seq.seq.word
 // Looks for paragraphs beginning with a word in break and returns seq of subsequences of paragraphs making up each block. In does this by creating a sequence of pairs of integers. Each pair contains beginning and end of a subsequence making up the block. //
 @(+, extractblock.a, empty:seq.seq.seq.word, finishpair(@(addpair, findparagraph(break, a), empty:seq.seq.int, arithseq(length.a, 1, 1)), length.a))

Function findlibclause(a:seq.seq.word, i:int)seq.word
 assert i < length.a report"No Library clause found"
 let s = a_i
  if s_1 = "Library"_1 then s else findlibclause(a, i + 1)

Function getlibraryinfo(libname:word)seq.seq.word
 let a = gettext.[ merge([ libname] + "/" + libname + ".ls")]
 let s = findlibclause(a, 1)
 let u = findindex("uses"_1, s, 3)
 let e = findindex("exports"_1, s, 3)
  [ // dependentlibs // subseq(s, u + 1, e - 1), // filelist // subseq(s, 2, min(u - 1, e - 1)), // exports // subseq(s, e + 1, length.s)]

Function getlibrarysrc(libname:word)seq.seq.word
 let filelist =(getlibraryinfo.libname)_2
  @(+, gettext2a(libname), empty:seq.seq.word, filelist)

function gettext2a(libname:word, a:word)seq.seq.word
 gettext.[ merge([ libname] + "/" + a + ".ls")]