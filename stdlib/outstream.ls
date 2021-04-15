Module outstream.T

use standard

use stack.seq.word

unbound +(T, char)T

unbound +(T, seq.char)T


    function addspace(nospace:boolean,result:T,toadd: word) T
           let i= findindex(toadd,specialwords:T)
            addspace2(nospace, result,toadd,false,i)


function specialwords:T seq.word [space]+'-()].:_^"' + "/br. ," 
 
     function addspace(nospace:boolean,result:T,toadd:seq.word) T
          for ns=nospace, a=result   ,  this=toadd do
             let i= findindex(this,specialwords:T)
           next(i < length.specialwords:T,  addspace2(ns, a,this,false,i))
           /for(a)


 function addspace2(nospace:boolean,a:T,this:word,escapehtml:boolean,i:int) T
     let wordseq=specialwords:T
    if i=length.wordseq then {, no space before but space after}   a + char1.","
    else if  i=length.wordseq-2  then{ /br   }  (a + char.10)
    else if  i=length.wordseq-1  then {. } a + char1."."+char.32
    else if i < length.wordseq then   { no space before or after }    (a + (decodeword.merge.wordseq)_i)
   else
    let d = decodeword.this
    let a1 = if nospace then a else a + char.32
     if escapehtml then
     for acc = a1, @e = d do acc
      + if @e = char1."<"then decodeword.first."&lt;"
      else if @e = char1."&"then decodeword.first."&amp;"else [ @e] /for(acc)
     else for acc = a1, @e = d do acc + @e /for(acc)
     
Function processpara(x:T, a:seq.word)T
 let specialwords=specialwords:T
 let none=merge."+NONE" 
 let match=merge."+MaTcH" 
 let pendingbreak=merge."+pendingBreak" 
  for nospace=false,result=x, stk=empty:stack.seq.word ,last=none, this=a+space do 
 if last=match then
    if this="/<"_1 then 
      next(false,addspace(nospace,result,this),push(stk,[this]),match)
    else if this="/>"_1 then
      if not.isempty.stk ∧  top.stk="/<"  then 
         next(false,addspace(nospace,result,this),pop.stk,match)
        else 
         next(false,result,stk,none)
    else 
       next(findindex(this,specialwords) < length.specialwords,addspace(nospace,result,this),stk,last)
 else if last=none then 
   next(nospace,result,stk,this)
 else if last = " /keyword"_1 then
    let toadd="<span class = keyword>" + this + "</span>"
    next (false,addspace(nospace,result,toadd), stk,none)
 else if last = " /em"_1 then
    let toadd="<em>" + this + "</em>"
    next (false,addspace(nospace,result,toadd), stk,none)
 else if last = " /strong"_1 then
     let toadd="<strong>" + this + "</strong>"
    next (false,addspace(nospace,result,toadd), stk,none)
 else if last = " /p"_1 then 
    next( false,addspace(nospace,result,EOL+"<p>"), stk,this)
   else if last = " /row"_1 then
   if not.isempty.stk ∧ top.stk = "</caption>"then
    let toadd= EOL + ' <tr><td> '+top.stk
    next(false,addspace(nospace,result,toadd), pop.stk,this)
    else
     let toadd= EOL + " <tr><td> "
    next(false,addspace(nospace,result,toadd), stk,this)
 else if last = " /cell"_1 then
    next(false,addspace(nospace,result,EOL + "<td>"), stk,this)
 else if last = " /br"_1 then
        if this /ne " /< "_1 then 
          let toadd=EOL + "<br>"+ space
          next(true,addspace(nospace,result,toadd),stk,this)
        else 
        next(nospace,result,stk,pendingbreak)
  else if last = " /<"_1 /or last=pendingbreak  then
  if this = "block"_1 then
     { if break is just before block suppress break }
     let toadd="<span class = block>" + space 
     next(true, addspace(nospace,result,toadd), push(stk,"</span>"),none)
 else  
   let pb=if last=pendingbreak then  EOL + "<br>" + space else ""
  if this = "noformat"_1 then
     next(nospace, result , stk,match)
 else if this=  "/section"_1 then
   let toadd=pb+EOL + "<h2>"+ space
      next(true, addspace(nospace,result,toadd), push(stk,"</h2>"),none)
 else if this = "table"_1 then
   let toadd=pb+"<table>" + space + "<caption>"
     next(false,addspace(nospace,result,toadd), push(push(stk,"</table>"),"</caption>"),this)
 else    
   let toadd=pb+"<span class =" + this + ">"
      next(false, addspace(nospace,result,toadd), push(stk,"</span>"),none)
 else if last= " />"_1 ∧ not.isempty.stk then
   let toadd=top.stk + space  
   next(true, addspace(nospace,result,toadd), pop.stk, if this=first."/br" then none else this)
 else if last = space then 
     let toadd= space 
    next( true,addspace(nospace,result,toadd), stk,this)
 else 
   let toadd= last let i= findindex(toadd,specialwords)
   next( i < length.specialwords,addspace2(nospace, result,toadd,true,i),stk,this)
 /for(if last=none then result else addspace(nospace,result,last))



