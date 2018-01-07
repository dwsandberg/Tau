Module core

use UTF8

use blockseq.int

use fileresult

use format

use libscope

use main

use prims

use seq.auths

use seq.icmd

use seq.int

use seq.liblib

use seq.libmod

use seq.libsym

use seq.mytype

use seq.session

use set.word

use sid

use stdlib

<<<<<<< HEAD
use fileio

Function main(user:UTF8, func:UTF8, a:UTF8)outputformat 
=======
Function main(user:UTF8, func:UTF8, a:UTF8)UTF8 
>>>>>>> parent of 874daae... Remove use of test.html
 let HTTP200 = [ 83, 116, 97, 116, 117, 115, 58, 32, 50, 48, 
  48, 32, 79, 75, 13, 10, 67, 111, 110, 116, 
  101, 110, 116, 45, 84, 121, 112, 101, 58, 32, 
  116, 101, 120, 116, 47, 104, 116, 109, 108, 13, 
  10, 13, 10]
  let func2 = fixup(toseqint.func, 1, empty:seq.int, empty:seq.seq.word)_1 
  let lib = func2_1 
  let user1 = towords.toseqint.user 
  let discard1 = loadlibrary.lib 
  let x = findFunction(lib, func2_3, func2_5, [ mytype."session", 
  mytype."word seq", 
  mytype."word seq", 
  mytype."word seq seq", 
  mytype."cmdresult"])
  let result = if not(length.x = 1)
   then"not authorized"+ func2 
   else if length.toseqint.a > 3 
   then let b = fixup(toseqint.a, findeq(toseqint.a, 1)+ 1, empty:seq.int, empty:seq.seq.word)
    theresult.cast2cmdresult.execute(x_1, cvtto.tosession(b_1_1, user1), b_3, b_4, subseq(b, 5, length.b))
   else theresult.cast2cmdresult.execute(x_1, cvtto.tosession("0"_1, user1),"","", empty:seq.seq.word)
<<<<<<< HEAD
   outputformat(HTTP200 + toseqint.toUTF8(htmlheader + result))

use fileio
 
 user
 
   UTF8.packedbyte(HTTP200 + toseqint.toUTF8(htmlheader + result))
  
   // assert false report "removed packedbyte function so main no longer works" //
=======
  // UTF8.packedbyte(HTTP200 + toseqint.toUTF8(htmlheader + result))//
   assert false report "removed packedbyte function so main no longer works"
>>>>>>> parent of 874daae... Remove use of test.html
    user

function cast2cmdresult(a:seq.word)cmdresult builtin

Function findeq(s:seq.int, i:int)int 
 if s_i = decode("="_1)_1 then i else findeq(s, i + 1)

function hexvalue(i:int)int if between(i, 48, 57)then i - 48 else i - 65 + 10

Function fixup(s:seq.int, i:int, result:seq.int, w:seq.seq.word)seq.seq.word 
 // assumes input format of <any char not including = > = <first arg>&<any char not including = > = <second arg> // 
  if i > length.s 
  then w + towords.result 
  else if subseq(s, i, i + 11)= [ 37, 48, 68, 37, 48, 65, 37, 48, 68, 37, 48, 65]
  then fixup(s, i + 12, empty:seq.int, w + towords.result)
  else let ch1 = s_i 
  if ch1 = decode("&"_1)_1 
  then fixup(s, findeq(s, i + 1)+ 1, empty:seq.int, w + towords.result)
  else if ch1 = decode("+"_1)_1 
  then fixup(s, i + 1, result + [ 32], w)
  else let ch = if ch1 = decode("%"_1)_1 then hexvalue(s_(i + 1))* 16 + hexvalue(s_(i + 2))else ch1 
  let increment = if ch1 = decode("%"_1)_1 then 3 else 1 
  fixup(s, i + increment, result + ch, w)

/ function auth(s:session, func:word)boolean let t = decode.func let a = findindex(decode("Z"_1)_1, t, 1)let b = findindex(decode("Z"_1)_1, t, a + 1)let thismodule = encodeword.subseq(t, a + 1, b-1)let lib = whichlib(s, thismodule)if length.lib = 0 then false else let discard = loadlibrary(lib_1)true

function cvtto(session)seq.word builtin

function findtitle(text:seq.word)seq.word 
 let start = findindex("&section"_1, text)
  let start2 = if start > length.text then findindex("Module"_1, text)else start 
  let finish = findindex("&}"_1, text, start2)
  subseq(text, start2 + 1, finish - 1)

type cmdresult is record sid:word, cmds:seq.icmd, text:seq.word, pos:seq.word

function theresult(a:cmdresult)seq.word 
 let script ="<script language =""javascript""type =""text/javascript""src =""myscript.js""></script>"
  let formhead ="<form id =""myform""name =""myform""autocorrect = off autocapitalize = off spellcheck = false action =""/tau""method = post>"
  script +"<title>"+ findtitle.text.a +"</title>"+"<div class = container> <nav class =""floating-menu"">"+ @(+, cmd7,"", cmds.a)+ formhead +"<input id = sid type = hidden name = sid value = '"+ sid.a +"'> <input id = func type = hidden name = func > <input id = selected type = hidden name = selected > <input id = lastselected type = hidden name = lastselected > <textarea id = txt name = txt style =""width:100% ;""rows = 1> </textarea> </form> </nav> <div class = content >"+ processpara.text.a +"</div></div>"+ if pos.a =""
   then""
   else"<script> document.getElementById("""+ pos.a +""").scrollIntoView()</script>"

Function cmdresult(sid:session, cmds:seq.icmd, text:seq.word)cmdresult 
 cmdresult(asword.sid, cmds, text,"")

Function cmdresult(sid:session, cmds:seq.icmd, text:seq.word, pos:seq.word)cmdresult 
 cmdresult(asword.sid, cmds, text, pos)

function cmd7(a:icmd)seq.word 
 let disable = if class.a ="inputnone"_1 then""else"disabled"
  assert length.funcname.a = 3 report"func format"+ funcname.a 
  {"<button class ="+ class.a + disable +"onclick =""javascript:cmd7("+ addquotes.[ funcname(a)_1,"."_1, funcname(a)_2,"."_1, funcname(a)_3]+","+ addquotes.arg.a +")"">"+ name.a +"</button>"}

type icmd is record name:seq.word, funcname:seq.word, class:word, arg:seq.word

Function icmd(name:seq.word, funcname:seq.word, class:word, arg:seq.word)icmd export

Function icmd(a:seq.word)icmd 
 assert length.a > 4 report"length of string must be longer:"+ a 
  icmd([ a_1], [ a_2, a_3, a_4], a_5, subseq(a, 6, length.a))

function addquotes(a:seq.word)seq.word 
 if length.a = 0 
  then"''"
  else if length.a = 1 
  then [ merge("'"+ a +"'")]
  else [ merge("'"_1, a_1)]+ subseq(a, 2, length.a)+"'"

_____________

function newsid(user:seq.word)session 
 let x = mapping.sessionencoding 
  let b = pseudorandom.if length.x > 0 then sid.last.x + hash.user else hash.user 
  decode(encode(session(b, user), sessionencoding), sessionencoding)

type session is record sid:int, user:seq.word

type sessionencoding is Encoding session

Function =(a:session, b:session)boolean sid.a = sid.b

Function hash(a:session)int sid.a

Function asword(a:session)word toword.sid.a

Function newsession(s:session)session newsid.user.s

Function user(session)seq.word export

Function tosession(w:word, user:seq.word)session 
 if w ="0"_1 
  then newsid.user 
  else decode(encode(session(toint.w,"x"), sessionencoding), sessionencoding)

function filter(a:set.word, l:liblib)seq.liblib 
 if libname(l)_1 in a then [ l]else empty:seq.liblib

function writeable(name:word, l:liblib)boolean libname(l)_1 = name ∧ not.readonly.l

function filter(name:word, m:libmod)seq.libsym 
 if name = modname.m then exports.m else empty:seq.libsym

function filter(fsigs:seq.word, s:libsym)seq.libsym 
 if fsig.s in fsigs 
  then let info = syminfo.s 
   if length.paratypes.info = 0 ∧ returntypeold.s = mytype."word seq"
   then [ s]
   else if returntypeold.s = mytype."cmdresult"then [ s]else empty:seq.libsym 
  else empty:seq.libsym

Function execute(s:session, funcname:word, modname:word, libname:word)cmdresult 
 assert"execute"_1 in checkauth(user.s, libname, modname)report"Not authorized to execute functions in"+ libname + modname 
  let fsigs = [ mangle(funcname, mytype.[ modname], empty:seq.mytype), 
  mangle(funcname, mytype.[ modname], [ mytype."session", 
  mytype."word seq", 
  mytype."word seq", 
  mytype."word seq seq"])]
  let l = @(+, findlib.[ libname], empty:seq.liblib, libs)
  let allsyms = @(+, filter.modname, empty:seq.libsym, mods(l_1))
  let syms = @(+, filter.fsigs, empty:seq.libsym, allsyms)
  // assert false report @(+, fsig,"", syms)+"fsigs"+ fsigs // 
  if returntypeold(syms_1)= mytype."word seq"
  then cmdresult(s, empty:seq.icmd, execute.fsig(syms_1))
  else cast2cmdresult.execute(fsig(syms_1), cvtto.s,"","", empty:seq.seq.word)

function findlib(libname:seq.word, l:liblib)seq.liblib 
 if libname.l = libname then [ l]else empty:seq.liblib

Function writemodule(s:session, libname:word, modname:word, newtext:seq.seq.word)seq.word 
 assert"write"_1 in checkauth(user.s, libname, modname)report"Not authorized to write"+ libname + modname 
  let discard = createfile([ merge([ libname]+"/changed")], ["a change"])
  let x = createfile([ merge([ libname]+"/"+ modname +".ls")], newtext)
  {"OK"}

Function readmodule(s:session, libname:word, modname:word)seq.seq.word 
 assert"read"_1 in checkauth(user.s, libname, modname)report"Not authorized to read"+ libname + modname 
  let name = [ libname]+"/"+ modname +".ls"
  if fileexists.name 
  then gettext.name 
  else ["Module"+ modname,"use stdlib"]

Function checkauth(user:seq.word, lib:word, mod:word)seq.word 
 let a = if"auth"_1 in @(+, libname,"", libs)
   then 0 
   else loadlib("auth", 0)
  execute("checkauthZauthZwordzseqZwordZword"_1, user, lib, mod)

