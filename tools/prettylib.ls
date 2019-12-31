Module prettylib

run prettylib testing2

use display

use fileio

use format

use libscope

use main2

use prettyparagraph

use renamemodule

use seq.tree.word

use stack.tree.word

use stacktrace

use stdlib

use textio

use tree.word

function plist(t:seq.word, i:int, parano:int, names:seq.word)seq.word 
   if i = 1 
   then 
    if length.names > 0 
    then"("+(if names_parano =":"_1 then""else [ names_parano]+":")
    + t_i 
    + plist(t, i + 1, parano + 1, names)
    else t 
   else if t_i =".a"_1 ∨ t_i =". a"_1 
   then subseq(t, i, i + 1)+ plist(t, i + 2, parano, names)
   else if parano ≤ length.names 
   then","+(if names_parano =":"_1 then""else [ names_parano]+":")
   + t_i 
   + plist(t, i + 1, parano + 1, names)
   else")"+ subseq(t, i, length.t)

Function testing2 seq.word 
  // htmlcode("stdlib")// 
  // callgraphwithin("testall","testall test11 test5 testencodings")doclibrary."stdlib"// 
  prettylib("stdlib2","")

Function prettylib(libname:seq.word, namemap:seq.word)seq.word 
  // Pretty prints lib source. // 
  // Warning:Discards text before first module. Multiple modules in the same file are broken into multiple files. // 
  // Will move a beginning comment inside parentheses and fail on(a + b)* b. // 
  // namemap is form changing module names in form"oldname1 newname1 oldname2 newname2..."// 
  // To avoid destroying source it is wise to map library name to a new directory and test to make sure pretty printing did not corrupt source. // 
  let discard = setmap.namemap 
    prettyit(firstPass(libname_1), [ mapname(libname_1),"/"_1], 1, [""])_1

function prettyit(lib:seq.seq.word, modname:seq.word, i:int, result:seq.seq.word)seq.seq.word 
   if i > length.lib 
   then 
    let x = createfile([ merge(modname +".ls")], result)
     ["Finished prettylib"]
   else 
    let p = lib_i 
    let key = p_1 
     if key in"module"
      then 
       let firstmod = length.modname < 3 
       let x = if firstmod then 0 else createfile([ merge(modname +".ls")], result)
       let name = mapname(p_2)
       let newfilename = subseq(modname, 1, max(length.modname - 1, 2))+ name 
        // assert false report newfilename // 
        prettyit(lib, newfilename, i + 1, [ processtotext("&keyword Module"+ name + subseq(p, 3, length.p))])
      else 
       let toadd = 
        if key in"use"
        then"&{ block &keyword use"+ mapname(p_2)+ subseq(p, 3, length.p)+"&}"
        else if key in"Library library"
        then 
         let u = findindex("uses"_1, p, 3)
         let e = findindex("exports"_1, p, 3)
          "&{ block &keyword Library"+ mapname(p_2)+ alphasort.@(+, mapname,"", subseq(p, 3, u - 1))
          +"&br &keyword"
          + subseq(p, u, e - 1)
          +"&br &keyword exports"
          + alphasort.@(+, mapname,"", subseq(p, e + 1, length.p))
          +"&}"
        else prettyparagraph.p 
        prettyit(lib 
        , modname 
        , i + 1 
        , if toadd =""then result else result + [ processtotext.toadd])

Function htmlcode(libname:seq.word)seq.word 
   let lib = firstPass(libname_1)
   let modules = @(+, findmodules,"", lib)
    "&{ noformat <h1> Source code for Library"+ libname +"</h1> &}"+ @(+, ref,"", modules)
    + @(+, prettyparagraph,"", lib)

Function ref(modname:word)seq.word"&{ noformat <a href = &quot"+ merge("#"_1, modname)+"&quot >"+ modname +"</a> &}"

function findmodules(p:seq.word)seq.word if p_1 ="module"_1 then [ p_2]else""

