Module makeentry
 
 use PEGnew
 
 use standard
 
 use set.word
 
 use otherseq.word
 
 use seq.seq.word
 
 Function modEntry(src:seq.seq.word) seq.word
 let tbl=maketable(
 " S Header {     options  #   \1 \2     # 
 /  Header  #   \1   #
 /br Header Function A2 (K P) TYPE  #   \1 \4 \length  \2 \3    #
/br * P, K # \0 /br \1  #  
/br K A1:TYPE # \1   \2 \length # / input:midpoint #  input files \length #
/br * A1 !:any # \1 # 
/br * A2 ! (any # \1 # 
/br TYPE boolean # boolean # / seq.word # words # / seq.file # files # 
 /br * desc  ! /br ! /p ! /strong ! *> ! <* ! } any # \0 \1 #
/br * options /strong any desc Discard <* block values *>  # \0  /br \push  \1 ?  \4 \2 \length \catleft # 
/             /strong any desc # \0  /br \push  \1 ? \2 \length \catleft #   
/             Discard      # \0  # 
/br * values  /strong desc # \0 \push  \1 \length \catleft # 
/          Discard2  #   \0   #
 /br * Discard2 <*   block N  *>  # # / Discard # #
 /br  * Discard <* ! block N  *>  # # / ! /strong ! <* ! *> ! } any #  #
 /br  *  N      <*         N  *>  # # /           ! <* ! *> ! } any # #
"
)
{???? code below contains hack for front and transform}
 for acc="",lastmod="?"_1,uses=empty:set.word,  p /in src do
 if subseq(p,1,1) ="Module" then
  next(acc,p_2,uses)
 else 
 if subseq(p,1,1) ="Function" /and  (lastmod /nin "tools" /or p_2 /nin "front transform" ) 
 /and p_2 /nin " getfiles "    then
  let a= run2(tbl,p)
  if subseq(a,1,1)="Fail" /or a_4 /nin "files" then  
   next(acc,lastmod,uses) else
    assert  a_4 /in "files" report "makentry" +p
  next(acc+ xxxx.postprocess.a ,lastmod,
  uses+ if lastmod /in "frontcmd transform" then "tools"_1 else lastmod)
 else 
  next(acc,lastmod,uses)
/do  
  if isempty.uses then "" else 
  "Module entrypoint
   /p use standard
   /p use file
   /p use llvmcode
   /p use seq.file
   /p use bits
   /p use seq.byte
   /p use process.UTF8
   /p use"
  + %("/p use", toseq.uses) >> 2
  + "/p Export addbcwords (seq.byte) int
   /p Function entrypoint (args:UTF8) UTF8
   /br let p = process.entrypoint2 (args),
   /br if aborted.p then finishentry.[file (
   $(dq."error.html"), message.p)] else result.p
   /p function entrypoint2 (args0:UTF8) UTF8
   /br let args = towords.args0,
   /br let cmd = first.args,
   /br let input = getfiles.args
   /br finishentry.$(acc << 2)
   /br else empty:seq.file"

 function xxxx(a:seq.seq.word) seq.word
 let cmd=[first.first.a]
   for txt2 = "", p ∈ a << 1 do
    let kind=p_2 let name=dq.[first.p]
    txt2
    + if kind  ∈ "words" then
     ", extractValue (args, $(name))"
    else if kind  ∈ "boolean" then
     ", first.$(name) ∈ extractValue (args, $(dq."flags"))"
    else if kind /in "files" then ""
    else
     ", ?"
   /do 
  "/br else if cmd /in $(dq.cmd) then 
  $(cmd) (input $(txt2))"
 
 
 function postprocess( a:seq.word ) seq.seq.word   
   for final=empty:seq.seq.word, acc="",count=-1,  last="?"_1,  w /in a+"X" do
     if count > 0 then
       next(final,acc+w,count-1,w)
     else if count=0   then  
       let newfinal  =  if  subseq(acc,2,2)="?" then 
             merge(final,acc)
           else final+acc
       next(newfinal , "",-1,w)
     else if last /in "~length" then
       next(final,acc,toint.w,w)
     else next(final,acc,count,w)
  /do final
  
function merge(a:seq.seq.word,b:seq.word) seq.seq.word
  for  acc=empty:seq.seq.word  ,  x /in a  do
   if first.x=first.b then
    acc+[subseq(x,1,2)+b << 2]
   else acc+x
/do acc
       
       
     
 
 
