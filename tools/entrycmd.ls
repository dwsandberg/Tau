Module entrycmd

use parseargs

use pretty

use standard

use textio

use seq.cmdinfo

use otherseq.word

use seq.seq.word

use process.seq.seq.word

function clean(p:seq.word, add:seq.word)seq.word
if p_2 = "command"_1 then
 let i = findindex(first." />", p)
 subseq(p, 1, 2) + subseq(p, i - 1, length.p)
else
 let b = break(p, "=, -", true)
 let a = 
  if first.b_2 = first."-"then subseq(p, length.b_1 + 1, length.p)
  else subseq(p, length.b_1, length.p)
 " /< block" + subseq(p, 1, 2) + a + " />"

function dq(s:seq.seq.word)seq.word
for txt = "", p ∈ s do txt + dq.p + ", "/for("[" + txt >> 1 + "]")

type cmdinfo is parano:int, cmdname:word, proc:seq.word, types:seq.seq.word, options:seq.word

function empty(d:seq.word, s:seq.word)seq.word if isempty.d then s else d

Function editwarning(filelist:seq.word)seq.word
"{This function was generated from the documentation in the files:" + dq.filelist
+ ". Manually editing this function is a bad idea.}"

function findcmd(p:seq.word)seq.word
let part = subseq(p, 3, findindex(first." />", p) - 1)
if length.part = 1 then part + part else part

function findoption(p:seq.word)seq.word
let part = subseq(p, 3, findindex(first." />", p) - 1)
let k = break(part, "-=", true)
assert length.k = 2 report"Error:syntax" + p
if first.k_2 = first."-"then subseq(k_2, 2, 2) + empty(first.k, "f")
else[last.first.k] + k_1 << 1

Function entry(libname:seq.word, html:boolean, includeproc:boolean, includedocin:boolean, optionsin:seq.word)seq.word
if not.isempty.optionsin then
 for options = "", types = empty:seq.seq.word, s ∈ break(optionsin, ", ", false)do next(options + first.s, types + s << 1)/for(let pp = parseargs(libname, options, types)
 "parseargs(" + dq.libname + ", " + dq.options + dq.types + ")"
 + for txt = "", o ∈ options do txt + " /br" + o + "=" + getarg(pp, o)/for(txt))
else
 let includedoc = if includeproc = false then true else includedocin
 {ship first part of file}
 let desc = 
  for desc = empty:seq.seq.word, name ∈ libname do
   let fullfile = breakparagraph.getfile:UTF8([name] + ".ls")
   for idx = 1, p ∈ fullfile while" /< command" ≠ subseq(p, 1, 2)do idx + 1 /for(desc + subseq(fullfile, idx, length.fullfile))
  /for(desc)
 let cmds = 
  for acc = empty:seq.cmdinfo
  , idx = 1
  , lastcmd = 0
  , options = ""
  , types = empty:seq.seq.word
  , p ∈ desc + " /< command a a  />"
  do
   let key = subseq(p, 1, 2)
   if key = " /< command"then
    if lastcmd = 0 then next(acc, idx + 1, idx, "", empty:seq.seq.word)
    else
     let t = desc_lastcmd
     let pp = findcmd.t
     let new = cmdinfo(lastcmd, {cmdname}last.pp, pp >> 1, types, options)
     next(acc + new, idx + 1, idx, "", empty:seq.seq.word)
   else if key = " /< option"then
    let pp = findoption.p
    next(acc, idx + 1, lastcmd, options + first.pp, types + pp << 1)
   else next(acc, idx + 1, lastcmd, options, types)
  /for(acc)
 {for txt="", c /in cmds do txt+" /p"+cmdname.c+proc.c+options.c+for txt2="", s /in types.c do txt2+dq.s+", "/for("types 
:["+txt2 >> 1+"]")/for(txt)}
 let doc = 
  if not.includedoc then""
  else
   for txt = "generated from" + libname + " /p"
   , cmdno = 1
   , inoption = false
   , p ∈ desc
   do
    let key = subseq(p, 1, 2)
    if key = " /< command"then
     let new = 
      clean(p, "")
      + if html ∧ not.isempty.options.cmds_cmdno then
       " /< noformat <input id="
       + merge([cmdname.cmds_cmdno] + "$" + space + "/" + ">")
       + " />"
      else""/if
      + if html then
       " /< noformat <button onclick=" + merge("cmd" + proc.cmds_cmdno)
       + "()>run cmd </button>  />"
      else""
     next(txt + " /p" + new, cmdno + 1, false)
    else if key = " /< option"then
     next(txt + " /p" + clean(p, "-"), cmdno, true)
    else
     let pp = 
      if subseq(p, 1, 1) ∈ ["Function", "function"]then pretty.p else p
     next(txt + " /p"
     + if inoption then" /< block" + pp + " />"else pp
     , cmdno
     , inoption
     )
   /for(txt)
 let proc = 
  if not.includeproc then""
  else
   " /< noformat <h2> Entry point procedure </h1>  />"
   + for txt = "", c ∈ cmds do
    let call = 
     if isempty.options.c then proc.c
     else if html then"let otherargs=getElementValue." + dq.[merge([cmdname.c] + "$")]
     else""/if
     + "let args=parseargs(otherargs, "
     + dq.options.c
     + ", "
     + dq.types.c
     + ")"
     + proc.c
     + for txt2 = "(", idx = 1, a ∈ options.c do
      let cc = 
       if first.(types.c)_idx ∈ "f"then"getarg:boolean(args, "
       else"getarg(args, "
      next(txt2 + cc + dq.[a] + "_1), ", idx + 1)
     /for(txt2 >> 1 + ")")
    txt
    + if html then
     pretty("Function" + merge("cmd" + proc.c) + "int" + editwarning.libname
     + "setElementValue("
     + dq."pageready"
     + ", "
     + call
     + ")")
     + " /p"
    else"if cmd=" + dq.[cmdname.c] + "then" + call + "else"
   /for(if html then txt
   else
    pretty("Function entrypoint(argin:UTF8)UTF8" + editwarning.libname
    + "let allargs=towords.argin let cmd=[first.allargs]let otherargs=allargs << 1 HTMLformat("
    + txt
    + dq."unknown command"
    + "+cmd)")/if)
 doc + proc

 /< command entry  /> Generate a command line interface for a library and provide documentation.

The format of the command line is  /< block command[word |-optionA(< words with balance parentheses>)|-optionB | optionC 
=<word>] />

The options define a set of option-value pairs. The values may zero or more words.

The  /em args of the command are the words not used to specify the options

The command"entry hello world"is equivalent to"entry-args(hello world)"

Some editors add extra args to shebang line. Anything after the second # will be treated as a comment.

The options the entry command takes are:

 /< option *-args  /> For-doc and-proc this is a list of files to use as source. The file extentsion".ls"will be added.

So the documentation can be provide at the end of a code file, only the part of the file starting with a paragraph starting with  /keyword  /<  /keyword 
command is used. 

 /< option-web  />

 /< option-proc  /> Produce entrypoint function.

 /< option-doc  /> Produce command documentation. If no options is specified this option is used.

 /< option *-option(<spec>, ..) /> Shows how the argments of a command are broken up. This option provides a list of the options 
. Each spec is the option name followed by the type  /br * zero or more words.  /br 1 exactly one word.  /br f no words; that is 
a flag set to true if option is present.  /br >0 one or more words.

A unix shell will treat some characters as special and may need to be escaped.  /< block tau stdlib simpletest entry-option\ 
(args *, c 1, b f \)-args\(arg1-b c=hello world\) />

 /< noformat <style> span.command{color:black ; font-size:120%; font-weight:bold;}span.block{padding:0px 0px 0px 
0px ; margin:0px 0px 0px 20px ; display:block ;}span.option{color:blue ;}</style>  /> 