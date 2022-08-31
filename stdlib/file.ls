Module file

use UTF8

use seq.bit

use bits

use bitstream

use seq.byte

use otherseq.char

use seq.seq.char

use seq.filename

use format

use standard

Export type:file

Export fn(file)filename

Export data(file)seq.byte

Export type:filename

type filename is dirpath:seq.word, name:word, ext:word

function dir(fn:filename)word
if length.dirpath.fn = 1 then first.dirpath.fn
else
 for acc = "", p ∈ dirpath.fn do acc + p + "/"/for(merge(acc >> 1))

Export name(filename)word

Export ext(filename)word

Export dirpath(filename)seq.word

function filename(dir:word, name:word, ext:word)filename filename([dir], name, ext)

Function fullname(fn:filename)word
merge.if dir.fn ∈ "."then[name.fn, "."_1, ext.fn]
else[dir.fn, "/"_1, name.fn, "."_1, ext.fn]

Export bs(file)bitstream

type file is fn:filename, data:seq.byte, bitdata:seq.bit, bs:bitstream

Export data(f:file)seq.byte

Export bitdata(f:file)seq.bit

Function file(fn:filename, a:seq.bit)file file(fn, empty:seq.byte, a, empty:bitstream)

Function file(name:seq.word, out:seq.word)file file(filename.name, out)

Function file(fn:filename, out:seq.word)file
{OPTION NOINLINE}
file(fn
, if ext.fn ∈ "html"then toseqbyte(toUTF8.htmlheader + HTMLformat.out)
else toseqbyte.textformat.out
)

Function file(fn:filename, a:seq.byte)file file(fn, a, empty:seq.bit, empty:bitstream)

Function file(fn:filename, a:seq.bits)file
let bs = tobitstream.a
file(fn, empty:seq.byte, empty:seq.bit, bs)

Function filename(s:seq.word)filename
let t = getfilenames("built", s)
assert length.t = 1 ∧ ext.first.t ∉ "?"report"illegal file name" + s
first.t

Function getfilenames(prefix0:seq.word, s:seq.word)seq.filename
let nofile = "."_1
for acc = empty:seq.filename
, filename = nofile
, last = "?"_1
, prefix = prefix0
, suffix = "?"_1
, w ∈ s
while w ∉ "="
do if w ∈ ".+"then next(acc, filename, w, prefix, suffix)
else if last ∈ "."then
 next(acc + fixfilename(prefix, filename, w), nofile, "?"_1, prefix, w)
else if last ∈ "+"then
 if filename = nofile then next(acc, nofile, "?"_1, [w], suffix)
 else next(acc + fixfilename(prefix, filename, suffix), nofile, "?"_1, [w], suffix)
else if filename = nofile then next(acc, w, last, prefix, suffix)
else next(acc + fixfilename(prefix, filename, suffix), w, last, prefix, suffix)
/for(if filename ≠ nofile ∧ w ∉ "="then acc + fixfilename(prefix, filename, suffix)else acc /if)

function fixfilename(prefix:seq.word, name:word, suffix:word)filename
let t = decodeword.name
let yy = break(char1."/", t)
if length.yy = 1 then filename(prefix, name, suffix)
else
 filename(encodeword(decodeword.first.prefix + char1."/" + t >> (length.last.yy + 1))
 , encodeword.last.yy
 , suffix
 )

Function changeext(f:filename, ext:seq.word)filename filename(dirpath.f, name.f, first.ext) 