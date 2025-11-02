/tag <h2> Building a Simple Web App /tag </h2>

Module webcmd

use UTF8

use frontcmd.callconfig

use JS.HTTPstate.cmdstate

use webHTTP.cmdstate

use file

use seq.file

use seq.seq.file

use seq1.filename

use seq.seq.filename

use real

use standard

use tau?

use webIO

use webIOtypes

use JS.HTTPstate.seq.word

use webHTTP.seq.word

This example shows how a command history can be implement and outlines how to construct a web application. The history will be kept in a history file. 

The file webcmd.html contains a small html fragment for this example. The lines of the body are:<* block <p id = status> loading<p>
/br <input id = cmdline value =" usegraph+built core.libsrc include: UTF8 words standard textio toWords" >
/br <button onclick =" runcmd ()" > run</button>
/br <table id = history
/br </table>
/br <p id = cmdno> 1 </p> *>

The first p element will be for a status line, the input element will be to enter a command, and the table element will be a history of the commands ran with links to the results. The final p element will be used to form the name of the next cmd output results. These compoents of the HTML file will be referenced by id from the file webcmd.ls which contains the Tau code. 

The line in the build file specifies the pieces needed for this example:<* block wasm webcore.libsrc tausupport core symbols compilerfront tools
/br+webapps webcallconfig.ls webcmd.ls webcmd.html
/br+tau2bc makescript.ls
/br Library: webcmd
/br exports: webcmd
/br output: webcmd.wasm *>

Web browser are constructed so control is giving back to the browser for reading and writing of files. A callback function is supplied to specify which procedure to execute when the operation is complete. User interaction in a web browser is captured as events. A callback for each event to be acted upon also needs a callback. This example uses the following callbacks:<* block /em webcmd is called when the page is loaded. The name of the callback (webcmd) matches the name of the page (webcmd). 
/br /em AddHistory is called after reading the history file when the page is loaded.
/br /em runcmd is called when the run button is pressed. The link between runcmd is specified with onclick =" runcmd ()" in webcmd.html
/br /em ExecuteCmd is called after reading the input files to the cmd.
/br /em createOutputFiles is called after write the output files of the cmd. *>

type cmdstate is
cmdline:seq.word
, filegroups:seq.int
, cmdAsEntered:seq.word
, input:seq.file {this type contains the information kept across callbacks.}

Function HTTPcmdline(h2:JS.HTTPstate.cmdstate, h:JS.HTTPresult) real decodeZ(h2, h)

function historyfilename filename
{name of history file}
filename."+built cmdhistory.txt"

Export HTTPwords(h2:JS.HTTPstate.seq.word, h:JS.HTTPresult) real

Function webcmd real
{called after web browser is finish loading webcmd.html. The name of this function must match the name of the webcmd.html file. }
let discard = setElementValue("status", "loading history"),
readfiles([file.historyfilename], "", "AddHistory")

use seq.word

Function AddHistory(p2:JS.HTTPstate.seq.word) real
{Callback for function simple. Takes contents of history file and puts in HTML page.}
let historyfiles = files.fromJS.p2,
if isempty.errors.historyfiles then
 let data = breakparagraph.historyfiles
 {data has three elements. The first is the filename, the second is the contents for the history table, and the third is the next next cmdno value}
 setElementValue("cmdno", data sub 3)
  + setElementValue("history", data sub 2)
  + setElementValue("status", "ready")
else
 setElementValue("history", "")
  + setElementValue("status", "no history :(errors.historyfiles)")

use seq.seq.word

Function runcmd real
{Command is called when button is pressed. 
/br fetchs input files with callback of" ExecuteCmd"}
let cmdstate = cmdstate.getElementValue."cmdline",
if isempty.cmdline.cmdstate then setElementValue("status", "No such command")
else HTTPcmdline(readarg(input.cmdstate, cmdstate, "ExecuteCmd", "HTTPcmdline"), empty:JS.HTTPresult)

Function ExecuteCmd(p2:JS.HTTPstate.cmdstate) real
{callback for function runcmd. This function takes the input files and cmd arguments and produces the result set of files. The files are written with the callback of createOutputFiles}
let s = fromJS.p2
let errors = errors.files.s,
if not.isempty.errors then setElementValue("status", "Errors in opening input files :(errors)")
else
 let cmdinfo = args.s
 let cmdno = getElementValue."cmdno"
 let outfiles =
  runthecmd(
   cmdline.cmdinfo + "output: + :(dirpath.historyfilename) :(cmdno).html"
   , filegroups(cmdinfo, files.s)
  )
 let newhistory =
  "/row cmd /sp /cell result
  /row :(cmdAsEntered.cmdinfo) /sp /cell :(href.outfiles) /row :(history)"
 let newcmdno = [toword(toint.cmdno sub 1 + 1)],
 let historyfile = file(historyfilename, " :(escapeformat) :(newhistory) :(escapeformat) /p :(newcmdno)"),
 setElementValue("status", "writing files")
  + setElementValue("history", newhistory)
  + setElementValue("cmdno", newcmdno)
  + HTTPcmdline(
  writearg(outfiles + historyfile, args.s, "createOutputFiles", "HTTPcmdline")
  , empty:JS.HTTPresult
 )

Function createOutputFiles(p2:JS.HTTPstate.cmdstate) real
{Callback ExecuteCmd. for Sets status in HTML page to hyperlinks to the files created}
setElementValue("status", "results:  :(href(files.fromJS.p2 >> 1))")

Function loadcmd(a:real) real
setElementValue("cmdline", getElementValue."ex. :(%(1, a))")

function cmdstate(cmdline0:seq.word) cmdstate
{create the state to be kept over callbacks from the command the user typed in. Filegroups are use to keep track of which file belongs to which argument of the command when the input files are scatter over many command arguments. }
let cmd = cmdline0 sub 1
for cmdline = "", b = empty:seq.seq.filename, e ∈ cmdDesc
while isempty.cmdline
do
 if cmd = e sub 1 then
  let cl = [cmd] + addDefaultName(cmdline0, e sub 2)
  for fs = empty:seq.seq.filename, p ∈ e << 2
  do fs + tofilenames.extractValue(cl, [p]),
  next(cl, fs)
 else next(cmdline, b)
for acc = empty:seq.file, filegroups = empty:seq.int, e ∈ b
do
 for acc2 = acc, fn ∈ e do acc2 + file.fn,
 next(acc2, filegroups + n.acc2),
cmdstate(cmdline, filegroups, cmdline0, acc)

function href(outfiles:seq.file) seq.word
{Create hyperlinks to output files}
for links = "", f ∈ outfiles
do
 let name = fullname.fn.f,
 links + "/sp /tag <a /sp href = :(merge("../" + name)) > :(name) /sp /tag </a> /sp",
links

function history seq.word
{Extract history from HTML page and convert it to a Tau sting using /sp /tag
/row /sp and /sp /tag /cell.}
let table = getElementValue."history"
for table0 = "", w ∈ subseq(table, 5, n.table - 1)
do
 if w ∈ "</td></tr><tr><td> </td></tr><tr><td></td></tr><tr><td>" then table0 + "/row"
 else if w ∈ "</td><td>" then table0 + "/sp /cell"
 else if w ∈ "<a </a>" then table0 + "/sp /tag :(w) /sp"
 else table0 + w,
table0

function filegroups(c:cmdstate, flat:seq.file) seq.seq.file
{Change format of input files to match that required by /em runthecmd function below}
for files = empty:seq.seq.file, last = 0, e ∈ filegroups.c
do next(files + subseq(flat, last, e), e),
files

<<<< Code Below was generated with command entrypoint tools.libsrc entryUses:webcallconfig frontcmd.callconfig core: >>>>

use webcallconfig

use usegraph

use PEGdebug

use tau?

use prettyScript

use frontcmd.callconfig

function cmdDesc seq.seq.word
[
 "front input input"
 , "transform input input link"
 , "unusedsymbols input input"
 , "PEGdebug input input"
 , "usegraph input input"
 , "buildhelp input input target"
 , "tau? cmd"
 , "prettyScript input input hashes"
]

function runthecmd(cmdline:seq.word, files:seq.seq.file) seq.file
let cmd = cmdline sub 1,
if cmd ∈ "front" then
 front:callconfig(
  files sub 1
  , extractValue(cmdline, "output o")
  , extractValue(cmdline, "pass")
  , extractValue(cmdline, "n")
  , extractValue(cmdline, "~n")
  , extractValue(cmdline, "mods")
  , extractValue(cmdline, "~mods")
  , extractFlag(cmdline, "within")
  , extractValue(cmdline, "out")
 )
else if cmd ∈ "transform" then
 transform:callconfig(
  files sub 1
  , files sub 2
  , extractValue(cmdline, "output o")
  , extractValue(cmdline, "target")
  , extractValue(cmdline, "modrename")
  , extractFlag(cmdline, "bind")
  , extractFlag(cmdline, "reorguse")
  , extractValue(cmdline, "html")
  , extractFlag(cmdline, "cleanexports")
  , extractFlag(cmdline, "moveexports")
  , extractValue(cmdline, "patternmods")
 )
else if cmd ∈ "unusedsymbols" then
 [
  file(
   extractValue(cmdline, "output o")
   , unusedsymbols:callconfig(
    files sub 1
    , extractFlag(cmdline, "all")
    , extractFlag(cmdline, "generated")
    , extractFlag(cmdline, "excessExports")
    , extractValue(cmdline, "ignore")
   )
  )
 ]
else if cmd ∈ "PEGdebug" then
 [
  file(
   extractValue(cmdline, "output o")
   , PEGdebug(files sub 1, extractValue(cmdline, "steps"), extractFlag(cmdline, "notable"))
  )
 ]
else if cmd ∈ "usegraph" then
 [
  file(
   extractValue(cmdline, "output o")
   , usegraph(
    files sub 1
    , extractValue(cmdline, "include")
    , extractValue(cmdline, "exclude")
    , extractValue(cmdline, "order")
   )
  )
 ]
else if cmd ∈ "buildhelp" then
 [
  file(
   extractValue(cmdline, "output o")
   , buildhelp(
    files sub 1
    , files sub 2
    , extractFlag(cmdline, "shellscript")
    , extractFlag(cmdline, "doc")
   )
  )
 ]
else if cmd ∈ "tau?" then
 [
  file(
   extractValue(cmdline, "output o")
   , tau?(extractValue(cmdline, "cmd"), extractValue(cmdline, "%"))
  )
 ]
else if cmd ∈ "prettyScript" then
 [
  file(
   extractValue(cmdline, "output o")
   , prettyScript(
    files sub 1
    , extractValue(cmdline, "builddir")
    , files sub 2
    , extractValue(cmdline, "roots")
    , extractValue(cmdline, "%")
   )
  )
 ]
else empty:seq.file 
