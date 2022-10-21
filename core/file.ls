Module file

use UTF8

use bits

use seq.byte

use otherseq.char

use seq.seq.char

use seq.filename

use format

use standard

use textio

Export type:file

Export fn(file) filename

Export rawdata(file) seq.seq.byte

Export type:filename

Export dirpath(filename) seq.word

Export ext(filename) word

Export name(filename) word

type filename is dirpath:seq.word, name:word, ext:word

function dir(fn:filename) word
if length.dirpath.fn = 1 then first.dirpath.fn
else for acc = "", p ∈ dirpath.fn do acc + p + "/" /for (merge(acc >> 1))

function filename(dir:word, name:word, ext:word) filename filename([dir], name, ext)

Function fullname(fn:filename) word
merge.if dir.fn ∈ "." then [name.fn, "."_1, ext.fn]
else [dir.fn, "/"_1, name.fn, "."_1, ext.fn]

type file is fn:filename, rawdata:seq.seq.byte, dummy:int

Function data(f:file) seq.byte
for acc = empty:seq.byte, e ∈ rawdata.f do acc + e /for (acc)

function file2(fn:filename, data:seq.seq.byte) file file(fn, data, 0)

Function file(name:seq.word, out:seq.word) file file(filename.name, out)

Function file(fn:filename, {C} out:seq.word) file
{OPTION NOINLINE}
{BXXX}
file(fn
, if ext.fn ∈ "html" then toseqbyte(htmlheader + HTMLformat.out)
else toseqbyte.textformat.out
)

Function file(fn:filename, a:seq.byte) file file2(fn, [a])

Function file(fn:filename, a:seq.seq.byte) file file2(fn, a)

Function filename(s:seq.word) filename
let t = getfilenames.s
assert length.t = 1 ∧ ext.first.t ∉ "?" report "illegal file name $(s + stacktrace)"
first.t

function =(a:filename, b:filename) boolean
dirpath.b = dirpath.a ∧ name.a = name.b ∧ ext.a = ext.b

Function %(a:filename) seq.word dirpath.a + name.a + "." + ext.a

Function getfilenames(s:seq.word) seq.filename
let nofile = "."_1
for acc = empty:seq.filename
, filename = nofile
, last = "?"_1
, prefix = "."
, suffix = "?"_1
, w ∈ s
while w ∉ "="
do
 if last ∈ "+" ∧ w ∈ "." then next(acc, filename, w, ".", suffix)
 else if w ∈ ".+" then next(acc, filename, w, prefix, suffix)
 else if last ∈ "." then
  next(if filename = nofile then acc else acc + fixfilename(prefix, filename, w)
  , nofile
  , "?"_1
  , prefix
  , w
  )
 else if last ∈ "+" then
  if filename = nofile then next(acc, nofile, "?"_1, [w], suffix)
  else
   next(acc + fixfilename(prefix, filename, suffix), nofile, "?"_1, [w], suffix)
 else if filename = nofile then next(acc, w, last, prefix, suffix)
 else next(acc + fixfilename(prefix, filename, suffix), w, last, prefix, suffix)
/for (
 if filename ≠ nofile ∧ w ∉ "=" then acc + fixfilename(prefix, filename, suffix)
 else acc)

function fixfilename(prefix:seq.word, name:word, suffix:word) filename
let t = decodeword.name
let yy = break(char1."/", t)
if length.yy = 1 then filename(prefix, name, suffix)
else
 filename(encodeword(decodeword.first.prefix + char1."/" + t >> (length.last.yy + 1))
 , encodeword.last.yy
 , suffix
 )

Function changeext(f:filename, ext:seq.word) filename
filename(dirpath.f, name.f, first.ext)

Function breakparagraph(fileseq:seq.file) seq.seq.word
for acc = empty:seq.seq.word, f ∈ fileseq do acc + breakparagraph.data.f /for (acc) 