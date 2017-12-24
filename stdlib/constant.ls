module constant

use buildtree

use seq.seq.word

use stdlib

type constant is record tocoding:encoding.seq.word

type constantencoding is encoding seq.word

Function constantmapping seq.seq.word mapping.constantencoding

Function encodeconstant(s:seq.word)constant constant.encode(s, constantencoding)

Function decode(c:constant)seq.word decode(tocoding.c, constantencoding)

Function encoding(c:constant)int encoding.tocoding.c

Function =(a:constant, b:constant)boolean encoding.a = encoding.b

Function addconst(w:seq.word)word toword.encoding.encodeconstant.w

Function getFREFinconstants seq.int @(+, getFREF(1, empty:seq.int), empty:seq.int, constantmapping)

Function getFREF(i:int, r:seq.int, d:seq.word)seq.int 
 if i > length.d 
  then r 
  else let t = d_i 
  if t in"LIT RECORD WORD CONST"
  then getFREF(i + 2, r, d)
  else assert t ="FREF"_1 report"UNEXPECTED CODE"+ t +"IN CONSTANT"+ d 
  getFREF(i + 2, r + funckey(d_(i + 1)), d)

