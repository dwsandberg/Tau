Module cmd2html

use file

use seq.file

use standard

use otherseq.word

use set.word

use seq.seq.word

function desc&options2(s:seq.word, i:int, result:seq.word, name:seq.word) seq.seq.word
if i > n.s then
["", result]
else if i_s ∉ "~length" then
[subseq(s, i, n.s), result]
else
 let newi = i + 2 + toint.(i + 1)_s,
 desc&options2(
  s
  , newi
  ,
   result
   + "/< br> /< label> /< input type = radio id =^(name) name =^(name) value =^((i + 2)_s)^(if isempty.result then "checked" else "")"
   + ">^(subseq(s, i + 3, newi - 1))"
   + "/< /label>"
  , name
 )

use set.seq.word

function ldq(s:seq.word) seq.word "/ldq^(s)^(dq)"

Function entrypoint(input:seq.file, o:seq.word) seq.word
{ENTRYPOINT}
modEntry.breakparagraph.input

Function cmd2html(input:seq.file, libname:seq.word, o:seq.word) seq.file
{ENTRYPOINT}
let outfn = filename.o
let outname = 1_libname
assert not.isempty.libname ∧ name.outfn ≠ 1_libname
report "libname cannot be empty or the same as o name"
let allsrc = breakparagraph.input
assert not.isempty.allsrc report "empty input"
let tbl = entrygrammar
for uses = empty:set.seq.word, code = "", txt = "", idx = 1, lastmod = "?", p1 ∈ allsrc
do
 if subseq(p1, 1, 1) = "Module" then
 next(
  uses
  , code
  , txt
  , idx
  , if subseq(p1, 3, 3) = "." then [2_p1] + ".callconfig" else [2_p1]
 )
 else
  let t = apply(tbl, p1),
   if isempty.t then
   next(uses, code, txt, idx, lastmod)
   else
    let cmdname = 1_1_t
    let callname = if 3_p1 ∈ ":" then [cmdname] + ":callconfig" else [cmdname]
    let cmddesc = 1_t << 2
    let args = t << 2
    let tmp =
     for codepara = "", txt2 = "", idxp = idx + 1, p ∈ args
     do
      let kind = 2_p
      let argname = 1_p
      let tmp2 = {desc&options (p, 3,"")} desc&options2(p, 3, "", id.idxp)
      let argdesc = 1_tmp2
      let options = 1^tmp2,
       if kind ∈ "boolean" then
       next(
        codepara + ", getElementValue.^(id.idxp) =^(dq."true")"
        ,
         txt2
         + "/br /< label> /< input type =^(ldq."checkbox") id =^(id.idxp) />^(argname)"
         + "/< /label>^(argdesc)"
        , idxp + 1
       )
       else
        let value = if argname ∈ "o" then "value =^(ldq."^(cmdname).html")" else "",
        next(
         codepara + ", getElementValue.^(id.idxp)"
         ,
          txt2
          + 
           if isempty.options then
           "/br /< label>^(argname) /< input id =^(id.idxp)^(value) /> /< /label>^(argdesc)"
           else
            {" /< select name =^(id.idxp) id =^(id.idxp) >^(options) /< /select>^(argdesc)"}
            "^(argdesc)^(options)"
         , idxp + 1
        )
     ,
     [
      codepara
      ,
       txt
       + "/p /< button onclick =^(ldq."runcmd1 (^(idx))") >^(cmdname) /< /button>^(cmddesc)"
       + "<* block^(txt2)"
       + "*>"
     ]
    let codepara = 1_tmp
    let para = 1^tmp,
    next(
     uses + lastmod
     ,
      code
      + "if cmdno =^(idx).0 then^(callname) (input^(codepara))
       /br else"
     , para
     , idx + 1 + n.args
     , lastmod
    )
assert not.isempty.txt report "No commands found in input"
let html =
 "/< p id = pageready> loading /< p> /< input id = input value =^(dq."+built core.libsrc")"
 + ">^(txt)"
let ls =
 other.outname
 + "/p use"
 + %("/p use", toseq.uses) >> 2
 + "/p Function runcmd2 (p2:JS.HTTPstate.real) int
  /br let s = fromJS.p2,
  /br let cmdno = args.s, let input = files.s
  /br let discard = setElementValue (^(dq."pageready"),^(dq("ready^" + "(print (3, cmdno))"))"
 + ") /br let files =^(code) empty:seq.file
  /br if isempty.files then
  /br setElementValue (^(dq) pageready^(dq),^(dq) no output^(dq))
  /br else
  /br let t = writefiles (files, 0.0,^(dq) runcmd3^(dq)), 0"
,
[
 file("+built^(outname).html", html)
 , file("+built^(outname).ls", ls)
 , file(outfn, "cmd2html created files: (outname).html^(outname).ls")
]

use otherseq.seq.word

function id(i:int) seq.word ldq.[merge.[1_"I", toword.i]]

Export +(seq.int, seq.int) seq.int

function other(outname:word) seq.word
"Module^(outname)
 /p use webHTTP.real
 /p use webIO
 /p use bits
 /p use seq.byte
 /p use file
 /p use standard
 /p use seq.file
 /p use JS.real
 /p use JS.HTTPstate.real
 /p use real
 /p use UTF8
 /p use otherseq.filename
 /p use webtools2
 /p Function runcmd1 (i:real) int
 /br let filenames = getfilenames (getElementValue.^(dq) input^(dq)),
 /br for acc = empty:seq.file, fn ∈ filenames do
 /br acc+file (fn, empty:seq.byte)
 /br, let discard = setElementValue (^(dq) pageready^(dq),^(dq) readyz^"
 + "(%n.filenames)^(dq))
 /br let z = readfiles (acc, i,^(dq) runcmd2^(dq)), 0
 /p Function runcmd3 (p2:JS.HTTPstate.real) int
 /br let links = for txt =^(dq)^(dq), f /in files.fromJS.p2 do
 /br let name = fullname.fn.f
 /br txt+^(dq)^(merge("/<" + space)) a href =^"
 + "(merge (^(dq)../^(dq)+name)) >^"
 + "(name)^(merge("/<" + space)) /a>^(dq), txt
 /br setElementValue (^(dq) pageready^(dq),^(dq) results: ^"
 + "(links)^(dq))
 /p Function^(outname) int setElementValue (^(dq) pageready^(dq),^(dq) ready^(dq))"

use makeentry 