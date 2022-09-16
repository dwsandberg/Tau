Module inputoutput

use UTF8

use bits

use seq.byte

use process.seq.byte

use seq.seq.byte

use file

use seq.file

use format

use standard

use tausupport

function tocstr(w:word)seq.byte
{returns 16 bytes of header followed by UTF8 bytes endding with 0 byte. }
packed(toseqbyte(emptyUTF8 + decodeword.w) + tobyte.0)

Builtin getbytefile2(seq.byte)process.seq.byte{OPTION STATE}

Function getfiles(args:seq.word)seq.file
for acc = empty:seq.file, fn ∈ getfilenames(args << 1)do
 let a = getbytefile2.tocstr.fullname.fn
 assert not.aborted.a report"Error openning file:" + fullname.fn
 acc + file(fn, result.merge(a, result.a + body2.a, empty:seq.byte))
/for(acc)

Builtin createfile3(data:seq.seq.byte, filename:seq.byte)int

___________

Function prepare(s:seq.seq.byte)seq.seq.byte
for acc = empty:seq.seq.byte, e ∈ s do
 if getseqtype.e = 1 then acc + e else acc + toseqseqbyte.e
/for(packed.acc)

Function finishentry(result:seq.file)UTF8
for acc = "files created:", f ∈ result do
 let discard2 = createfile3(prepare.rawdata.f, tocstr.fullname.fn.f)
 acc + fullname.fn.f
/for(HTMLformat.acc) 