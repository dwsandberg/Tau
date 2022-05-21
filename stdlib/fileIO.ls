Module fileIO

use bits

use file

use format

use inputoutput

use standard

use seq.bit

use seq.byte

use seq.file

use seq.seq.bit

use seq.seq.byte

Function check(s:seq.seq.byte)boolean
for acc = getseqtype.s = 0, p ∈ s while acc do getseqtype.p = 1 /for(acc)

Function finishentry(result:seq.file)UTF8
for acc = "files created:", f ∈ result do
 let discard2 = 
  if check.xdata.f then createfile3(packed.xdata.f, tocstr.[fullname.fn.f])
  else createfile([fullname.fn.f], data.f)
 acc + fullname.fn.f
/for(HTMLformat.acc)

Function getfiles(args:seq.word)seq.file
for acc = empty:seq.file, fn ∈ getfilenames(".", args << 1)do
 acc
 + if ext.fn ∈ "bc"then file(fn, empty:seq.seq.byte, [getfile:bit([fullname.fn])])
 else file(fn, [getfile:byte([fullname.fn])], empty:seq.seq.bit)
/for(acc)

function getfile(fn:filename)file file(fn, [getfile:byte([fullname.fn])], empty:seq.seq.bit) 