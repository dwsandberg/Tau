Module entrycmd

use standard

use parseargs

use textio

use pretty

use standard

use seq.cmdinfo

use otherseq.word

function clean(p:seq.word, add:seq.word)seq.word
let i = findindex(first." />", p)
" /p"
+ if p_2 ∉ "option"then subseq(p, 1, 2) + subseq(p, i - 1, length.p)
else
 " /< block" + subseq(p, 1, 2) + "-" + subseq(p, i - 1, length.p)
 + " />"

function quote(s:seq.word)seq.word '"' + s + '"'

type cmdinfo is parano:int, cmdname:word, proc:seq.word, types:seq.word, options:seq.word

function empty(d:seq.word, s:seq.word)seq.word if isempty.d then s else d

use process.seq.seq.word

function parse(t:seq.word, options:seq.word, types:seq.word)seq.seq.word
let j = findindex(first." />", t)
let p = process.parseargs(subseq(t, 3, j - 1), options, types)
if aborted.p then
 assert false report"error" + message.p + "in" + t
 [""]
else result.p

Function editwarning(filelist:seq.word)seq.word
"{This function was generated from the documentation in the files:'" + filelist
+ "'. Manually editing this function is a bad idea.}"

Function entry(libname:seq.word
, html:boolean
, includeproc:boolean
, includedocin:boolean
, optionsin:seq.word
, typesin:seq.word
)seq.word
if not.isempty.optionsin then
   if  optionsin = "run tests" then testX
   else 
   assert length.optionsin=length.typesin report "options and types must be of equal length"
   for txt="",p /in parseargs(libname,   optionsin ,typesin) do
     txt+p+"/br"
     /for(txt)
else 
let includedoc=if includeproc=false then true else includedocin
let desc = 
   for desc=empty:seq.seq.word,       name /in libname do
     let fullfile=   breakparagraph.getfile:UTF8([name]+".ls")    
   for idx = 1, p ∈ fullfile while" /< command" ≠ subseq(p, 1, 2)do idx + 1 /for(desc+subseq(fullfile, idx, length.fullfile))
   /for(desc)
let cmds=
for acc=empty:seq.cmdinfo,idx=1,lastcmd=0,options=""
, p ∈ desc+ "/< command a a />"
do
 let key = subseq(p, 1, 2)
 if key = " /< command"then 
  if lastcmd=0 then next(acc,idx+1,idx,"")
  else 
   let argtypes = reverse( options >> (length.options / 2))
  let validargs = options << (length.options / 2)
  let t=desc_lastcmd
      let pp=parse(t,"main f","word word")
      let cmdname=  first.getarg(pp,"main"_1) 
   let new=cmdinfo(lastcmd,cmdname, empty(getarg(pp,"f"_1)  ,[cmdname] ) ,argtypes,validargs)
     next(acc+new,idx+1,idx,"")
 else if key = " /< option"then 
   let pp=parse(p,"main  t","word word")
 next(acc,idx+1,lastcmd, empty(getarg(pp,"t"_1),"words") + options + getarg(pp,"main"_1)_1)
 else next(acc,idx+1,lastcmd, options)
 /for(acc)
 { for txt="",c /in cmds do 
   txt+"/br"+cmdname.c+proc.c+options.c+types.c
/for(txt) }
let doc=if not.includedoc then "" else 
for txt = "generated from " +  libname +" /p"
, cmdno=1,p ∈ desc
do
 let key = subseq(p, 1, 2)
 if key = " /< command"then 
 let new= clean(p, "") +
   if html /and not.isempty.options.cmds_cmdno then 
       "/< noformat <input id=" +merge([ cmdname.cmds_cmdno]+"$"+space +"/"+">")+ "/>"  
      else "" /if
   +if html then 
   "/< noformat <button onclick="+merge("cmd"+proc.cmds_cmdno)
   +"()>run cmd </button> />" 
   else "" 
  next(txt+new,cmdno+1)
 else if key = " /< option"then  next(txt + clean(p, "-"),cmdno)
  else next(txt + " /p" + p,cmdno)
/for(txt)
let proc=if not.includeproc then "" else" /< noformat <h2> Entry point procedure </h1>  />"
+  
for txt = ""
,c ∈ cmds
do
    let call =  
     if isempty.options.c then proc.c
     else 
      (if html then 
       " let otherargs=getElementValue."+quote.[merge([cmdname.c]+"$")]
      else "")+
     "let args=parseargs(otherargs, "
    + quote.options.c
    + ", "
    + quote.types.c
    + ")" +proc.c+
       for txt2 = "(", idx = 1, a ∈ options.c do
        let cc= if (types.c)_idx /in "boolean" then "getarg:boolean(args,"
        else "getarg(args, "
       next(txt2 + cc + quote.[a] + "_1), ", idx + 1)
      /for(txt2 >> 1 + ")") 
    txt+ if html then 
     pretty("Function "+merge("cmd"+proc.c)  
     + " int "+editwarning.libname+ ' setElementValue("pageready",
    ' +call+")")+"/p"
    else "if cmd=" + quote.[cmdname.c] + "then" + call  + "else"
/for(if html then txt else
    pretty("Function entrypoint(argin:UTF8)UTF8"+editwarning.libname+" let allargs=towords.argin let cmd=[first.allargs]
    let otherargs=allargs 
<< 1 HTMLformat("
+
txt
+ '"unknown command"+cmd )'))
doc+proc


   /< command -f entry  entry /> Generate a command line interface for a library and provide documentation.
  
  Some editors add extra args to shebang line.  Anything after the second # will be treated as a comment.
 
  /< option -t words main  />  For -doc and -proc this is a list of files to use as source. The file extentsion ".ls" will be added.
  
  So the documentation can be provide at the end of a code file,  only
  the part of the file starting with a paragraph starting with /keyword /< /keyword command  is used. 
 
  /< option -t boolean web  />
  
  /< option -t boolean proc  /> Produce entrypoint function.
 
  /< option -t boolean doc  />  Produce command documentations.  If nooptions is specified this option is used.
  
   /< option -t words option  />  Shows how the argments of a command are broken up. This option
   provides a list of the option names.  Must be used with the -types option to specify the types of the options.
   BUG! cannot escape options!!!!
   
   If "-option run test" is used then a set of tests for the command line parser is ran.
   
 /< option -t words types  />  Specifies the types of options for the -option option. Valid types are
    word words and boolean

 /< noformat <style> span.command{color:black ; font-size:120%; font-weight:bold;}span.block{padding:0px 0px 0px 
0px ; margin:0px 0px 0px 20px ; display:block ;}span.option{color:blue ;}</style>  /> 


