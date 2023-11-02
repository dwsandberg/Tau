Module file

use UTF8

use bits

use seq.byte

use otherseq.char

use seq.seq.char

use seq.filename

use format4

use format1

use standard

use textio

Export textFormat1(myinput:seq.word) UTF8

Export HTMLformat1(myinput:seq.word) UTF8

Function HTMLformat(s:seq.word) UTF8 HTMLformat1.s

Export type:file

Export fn(file) filename

Export rawdata(file) seq.seq.byte

Export type:filename

Export dirpath(filename) word

Export ext(filename) word

Export name(filename) word

Export HTMLformat(seq.word) UTF8

Function textformat(s:seq.word) UTF8 textFormat4.s

type filename is dirpath:word, name:word, ext:word

Function fullname(fn:filename) word
merge.
 if dirpath.fn ∈ "." then
 [name.fn, 1#".", ext.fn]
 else [dirpath.fn, 1#"/", name.fn, 1#".", ext.fn]

type file is fn:filename, rawdata:seq.seq.byte, dummy:int

Function data(f:file) seq.byte for acc = empty:seq.byte, e ∈ rawdata.f do acc + e, acc

Function file(name:seq.word, out:seq.word) file file(filename.name, out)

Function file(fn:filename, out:seq.word) file
{OPTION NOINLINE}
file(
 fn
 , if ext.fn ∈ "html" then
  toseqbyte(HTMLheader + HTMLformat.out)
  else toseqbyte.textformat.out
)

Function file(fn:filename, a:seq.byte) file file(fn, [a], 0)

Function file(fn:filename, a:seq.seq.byte) file file(fn, a, 0)

Function filename(s:seq.word) filename
let t = tofilenames.s
assert n.t = 1 ∧ ext.1#t ∉ "?" report "illegal file name^(s + stacktrace)",
1#t

function =(a:filename, b:filename) boolean
dirpath.b = dirpath.a ∧ name.a = name.b ∧ ext.a = ext.b

Function %(a:filename) seq.word [dirpath.a, name.a, 1#".", ext.a]

Function tofilenames(s:seq.word) seq.filename
let nofile = 1#"."
for
 continue = true
 , acc = empty:seq.filename
 , filename = nofile
 , last = 1#"?"
 , prefix = "."
 , suffix = 1#"?"
 , w ∈ s
while continue
do
 if last ∈ "+" ∧ w ∈ "." then
 next(continue, acc, filename, 1#"?", ".", suffix)
 else if w ∈ ".+" then
 next(continue, acc, filename, w, prefix, suffix)
 else if last ∈ "." then
 next(
  continue
  , if filename = nofile then acc else acc + fixfilename(prefix, filename, w)
  , nofile
  , 1#"?"
  , prefix
  , w
 )
 else if last ∈ "+" then
  if filename = nofile then
  next(continue, acc, nofile, 1#"?", [w], suffix)
  else next(continue, acc + fixfilename(prefix, filename, suffix), nofile, 1#"?", [w], suffix)
 else if filename = nofile then
 next(continue, acc, w, last, prefix, suffix)
 else next(continue, acc + fixfilename(prefix, filename, suffix), w, last, prefix, suffix),
if filename ≠ nofile ∧ continue then acc + fixfilename(prefix, filename, suffix) else acc

function fixfilename(prefix:seq.word, name:word, suffix:word) filename
let t = decodeword.name
let yy = break(char1."/", t),
if n.yy = 1 then
filename(1#prefix, name, suffix)
else filename(
 encodeword(decodeword.1#prefix + char1."/" + t >> (n.1^yy + 1))
 , encodeword.1^yy
 , suffix
)

Function addDefaultName(argsin:seq.word, first:word) seq.word
let args = argsin << 1
let len = n.args,
if len > 1 ∧ 2#args ∈ ":=" ∨ len = 0 then args else "^(first):" + args

Function changeext(f:filename, ext:seq.word) filename filename(dirpath.f, name.f, 1#ext)

Function breakparagraph(fileseq:seq.file) seq.seq.word
for acc = empty:seq.seq.word, f ∈ fileseq do acc + breakparagraph.data.f,
acc

Function HTMLheader UTF8
{the format of the meta tag is carefully crafted to get math unicode characters to display correctly}
textformat."<!doctype html> <meta charset =^(dq."UTF-8") ><style>
/br <!--span.avoidwrap {display:inline-block ;} span.keyword {color:blue ;}
/br span.literal {color:red ;} span.comment {color:green ;}
/br span.block {padding:0px 0px 0px 0px ; margin:0px 0px 0px 20px ; display:block ;}
/br--> </style>" 