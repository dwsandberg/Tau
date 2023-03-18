Module cmd2html

use file

use seq.file

use standard

use otherseq.word

use set.word

use seq.seq.word

use PEG




function desc&options(s:seq.word,i:int,result:seq.word) seq.seq.word
   if i > length.s  then  ["",result]
   else if s_i /nin " ~length" then  [subseq(s,i,length.s),result]
   else let newi=i+2+toint.s_(i+1)
     desc&options(s,newi,
     result+"<option value = $(s_(i+2)) > $(subseq(s,i+3,newi-1)) </option>")
 
 use set.seq.word    
 
Function cmd2html(input:seq.file, moduleRename:seq.word, libname:seq.word, o:seq.word) seq.file
{ENTRYPOINT}let outfn = filename.o 
let outname=first.libname
assert not.isempty.libname ∧ name.outfn ≠ first.libname
report "libname cannot be empty or the same as o name"
  let allsrc=breakparagraph.input
assert not.isempty.allsrc  report "empty input"
 let tbl=entrygrammar
  for uses = empty:set.seq.word, code = "", txt = "", idx = 1,lastmod="?", p1 ∈ allsrc do
     if subseq(p1,1,1) ="Module" then
  next(uses,code,txt,idx, if subseq(p1,3,3)="." then [p1_2] +".callconfig" else [p1_2] )
 else 
  let t=apply(tbl,p1)  
 if isempty.t    then 
  next(uses,code,txt,idx,lastmod ) 
  else
   let cmdname=  first.first.t 
   let callname=if p1_3 /in ":" then [cmdname] +":callconfig" else [cmdname]
   let cmddesc= first.t << 2
   let args=t << 2
 let tmp= for codepara = "",txt2="", idxp = idx + 1, p ∈ args do
      let kind=p_2
   let argname=p_1
   let tmp2=desc&options(p,3,"")
   let argdesc=first.tmp2
   let options=last.tmp2
   if kind  ∈ "boolean" then
    next(codepara + ", getElementValue.$(id.idxp) = $(dq."true")"
    , txt2+    "<* none <br> <label> $(argname) <input type = $(dq."checkbox") id = $(id.idxp) /> </label> *> $(argdesc)"
     , idxp + 1)
   else
        let value = if argname ∈ "o" then "value = $(dq."$(cmdname).html")" else "",
    next(codepara + ", getElementValue.$(id.idxp)"
    ,txt2+   if isempty.options then    "<* none <br> <label> $(argname) <input id = $(id.idxp) $(value) /> </label> *> $(argdesc)"
       else   "<* none <select name = $(id.idxp) id = $(id.idxp) > $(options) </select> *> $(argdesc)"
   , idxp + 1)
  /do [codepara, txt + "/p <* none <button onclick = $(dq."runcmd1 ($(idx))") > $(cmdname) </button> *> $(cmddesc) <* block $(txt2) *>"
]
   let codepara = first.tmp
   let para=last.tmp
   next(uses + lastmod
  , code + "if cmdno = $(idx).0 then $(callname) (input $(codepara)) /br else"
  , para
  , idx + 1 + length.args,lastmod)
/do
assert not.isempty.txt report "No commands found in input"
 let html = 
  "<* none <p id = pageready> loading <p> <input id = input value = $(dq."+built core.libsrc") > *>" + txt
 let ls = 
  other.outname + "/p use" + %("/p use", toseq.uses) >> 2
  + "/p Function runcmd2 (p2:JS.HTTPstate.real) int
   /br let s = fromJS.p2,
   /br let cmdno = args.s, let input = files.s
   /br let discard = setElementValue ($(dq."pageready"),
   $(dq."ready $("$") (print (3, cmdno))"))
   /br let files = $(code) empty:seq.file
   /br if isempty.files then
   /br setElementValue ($(dq) pageready $(dq), $(dq) no output $(dq))
   /br else
   /br let t = writefiles (files, 0.0,
   $(dq) runcmd3 $(dq)), 0"
 ,
 [file("+built $(outname).html", html), file("+built $(outname).ls", ls), file(outfn, "done")]

 use otherseq.seq.word


function id(i:int) seq.word dq.[merge.["I"_1, toword.i]]

Export +(seq.int, seq.int) seq.int

function other(outname:word) seq.word
"Module $(outname)
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
 /br let filenames = getfilenames (getElementValue.$(dq) input $(dq)),
 /br for acc = empty:seq.file, fn ∈ filenames do
 /br acc+file (fn, empty:seq.byte)
 /br /do let discard = setElementValue ($(dq) pageready $(dq), $(dq) readyz $("$")
 (%n.filenames) $(dq))
 /br let z = readfiles (acc, i,
 $(dq) runcmd2 $(dq)), 0
 /p Function runcmd3 (p2:JS.HTTPstate.real) int
 /br let links = for txt = $(dq) $(dq), f /in files.fromJS.p2 do
 /br let name = fullname.fn.f
 /br txt+$(dq) <a href = $("$") (merge ($(dq)../ $(dq)+name)) > $("$") (name) </a> $(dq)
 /do txt
 /br setElementValue ($(dq) pageready $(dq), $(dq) results: $(merge("< *" + space)) none
 $("$") (links) $(merge("* >" + space)) $(dq))
 /p Function $(outname) int setElementValue ($(dq) pageready $(dq), $(dq) ready $(dq))" 
 
 use makeentry
 
 