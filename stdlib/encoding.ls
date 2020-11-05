Module encoding.T

use blockseq.T

use seq.T

use seq.encodingpair.T

use seq.seq.encodingpair.T

use stdlib

use otherseq.encodingpair.T

use otherseq.seq.encodingpair.T

use process.T

use blockseq.encodingpair.T


Function type:encodingpair.T internaltype export

Function type:encoding.T internaltype export

Function type:encodingstate.T internaltype export

type encodingstate is sequence length:int, encodetable:seq.seq.encodingpair.T, decodetable:seq.seq.encodingpair.T, all:seq.encodingpair.T


Function length(e:encodingstate.T)int export

Function_(e:encodingstate.T, i:int)T data.(all.e)_i


type encodingpair is record code:encoding.T, data:T, hash:int

Function code(a:encodingpair.T)encoding.T export

Function data(a:encodingpair.T) T   export

Function encodingpair(code:encoding.T,data:T) encodingpair.T encodingpair( code,data,hash.data)

Function hash(a:encodingpair.T)int  export

Function =(a:encodingpair.T, b:encodingpair.T)boolean
 hash.a = hash.b ∧ valueofencoding.code.a = valueofencoding.code.b
 ∧ data.a = data.b
  
 Function ?(a:encodingpair.T, b:encodingpair.T)ordering valueofencoding.code.a ? valueofencoding.code.b

Function hash(T)int unbound

Function =(T, T)boolean unbound

Function empty:encodingstate.T encodingstate.T
let x = constantseq(4, empty:seq.encodingpair.T)
 encodingstate(0, x, x, empty:seq.encodingpair.T)

function adddata(eletoadd:encodingpair.T, tablesize:int, a:encodingpair.T)seq.encodingpair.T
 if data.a = data.eletoadd &or hash.eletoadd mod tablesize ≠ hash.a mod tablesize then
 empty:seq.encodingpair.T
 else [ a]

function addcode(code:encoding.T, hashsize:int, x:seq.encodingpair.T, e:encodingpair.T)seq.encodingpair.T
 if code.e = code ∨ valueofencoding.code mod hashsize ≠ valueofencoding.code.e mod hashsize then
 x
 else x + e

type encoding is record valueofencoding:int

Function valueofencoding(a:encoding.T)int export

Function to:encoding.T (i:int)  encoding.T  encoding.i


Function lastadded( h:encodingstate.T) encoding.T
   code.last.all.h

Function add(h:encodingstate.T, v:encodingpair.T)encodingstate.T
 // this is the add that is stored in the erecord //
 let tablesize = length.encodetable.h
  if 3 * length.h > 2 * tablesize then
  let t = encodetable.h
   let d = decodetable.h
    add(encodingstate(length.h, t + t + t + t, d + d + d + d, all.h)
    , v)
  else
   let datahash = hash.v
   let dataindex = datahash mod tablesize + 1
    if @(max, ele.data.v, 0,(encodetable.h)_dataindex) > 0 then // already present // h
    else 
     let p=subadd(h,v,1)
          let codeindex = valueofencoding.code.p mod tablesize + 1
      let l1=@(addcode(code.p, tablesize), identity, [ p],(decodetable.h)_codeindex)
     let l2= @(+, adddata(p, tablesize), [ p],(encodetable.h)_dataindex)
     let newdecodetable = replace(decodetable.h, codeindex, l1)
     let newencodetable = replace(encodetable.h, dataindex, l2)
      encodingstate(length.h + 1, newencodetable,newdecodetable , all.h + p)



function used(t:encoding.T, a:encodingpair.T) int
 if t = code.a then 1  else 0
 
 function subadd(h:encodingstate.T, v:encodingpair.T,count:int) encodingpair.T
    // assert count < 10 report "unable to assign encoding" //
    let tablesize = length.encodetable.h
    let code = code.v
    let codeindex = valueofencoding.code mod tablesize + 1
    let found=  valueofencoding.code.v ≤ 0 &or @(+, used.code.v,0,(decodetable.h)_(codeindex) ) > 0
    if found then subadd(h, encodingpair(to:encoding.T(assignencoding(length.h,data.v)), data.v, hash.v),count+1)
     else encodingpair(code.v, deepcopy.data.v, hash.v)

Function assignencoding(length:int,data:T) int // (randomint.1)_1 // unbound

Function assignrandom(length:int,data:T) int  (randomint.1)_1


Function addencodingpairs(l:seq.encodingpair.T) encodingstate.T
                  @(add,rehash,getinstance:encodingstate.T,l)

function rehash(a:encodingpair.T) encodingpair.T encodingpair(code.a,data.a)




 
Function lookupencodingpair(t:encoding.T) seq.encodingpair.T
let inst = getinstance:encodingstate.T
  decode(inst, t)
 

Function decode(t:encoding.T) T
 let inst = getinstance:encodingstate.T
 let a = decode(inst, t)
  assert length.a = 1 report"no such encoding" + toword.valueofencoding.t+stacktrace
   data.a_1

use seq.encodingstate.T

Function getinstance:encodingstate.T encodingstate.T  builtin.usemangle

Function primitiveadd(s:encodingpair.T)  int builtin.usemangle




Function encoding:seq.encodingpair.T  seq.encodingpair.T  
 all.getinstance:encodingstate.T 

use seq.encodingpair.T

Function encode(t:T)encoding.T
 let r = lookuprep(t, getinstance:encodingstate.T)
  if isempty.r then
  let discard = primitiveadd( encodingpair(to:encoding.T(0), t, hash.t))
    encode(t)
  else code.r_1
  



function decode(h:encodingstate.T, t:encoding.T)seq.encodingpair.T
 @(+, ele4.t, empty:seq.encodingpair.T,(decodetable.h)_(valueofencoding.t mod length.decodetable.h + 1))

function ele4(t:encoding.T, a:encodingpair.T)seq.encodingpair.T
 if t = code.a then [ a]else empty:seq.encodingpair.T




use stacktrace 

Function =(a:encoding.T, b:encoding.T)boolean valueofencoding.a = valueofencoding.b

Function ?(a:encoding.T, b:encoding.T)ordering valueofencoding.a ? valueofencoding.b

Function hash(a:encoding.T)int valueofencoding.a



function lookuprep(t:T, inst:encodingstate.T)seq.encodingpair.T
 @(+, ele5.t, empty:seq.encodingpair.T,(encodetable.inst)_(hash.t mod length.encodetable.inst + 1))

function ele(v:T, a:encodingpair.T)int if v = data.a then valueofencoding.code.a else 0



Function type:encodingpair.T internaltype export

function ele5(v:T, a:encodingpair.T)seq.encodingpair.T if v = data.a then [ a]else empty:seq.encodingpair.T

  
  Function findencode( t:T)seq.T
 let r = lookuprep(t, getinstance:encodingstate.T)
  if isempty.r then empty:seq.T else [ data.r_1]


Function analyze(t:encodingstate.T)seq.word
 "numele =" + toword.length.all.t + "encodecounts" + counts(encodetable.t, 1, 0, 0, 0)
 + "decodeconuts"
 + counts(decodetable.t, 1, 0, 0, 0)

function counts(s:seq.seq.encodingpair.T, i:int, one:int, two:int, big:int)seq.word
 if i > length.s then @(+, toword,"", [ length.s, one, two, big])
 else
  let t = length.s_i
   if t = 0 then counts(s, i + 1, one, two, big)
   else if t = 1 then counts(s, i + 1, one + 1, two, big)
   else if t = 2 then counts(s, i + 1, one, two + 1, big)
   else counts(s, i + 1, one, two, big + 1)
   
   
module assignencodingnumber 

use stdlib

use encoding.typename

type  typename is record name:seq.word

function =(a:typename,b:typename) boolean  name.a=name.b

function hash(a:typename) int hash.name.a


Function  encodingno(name:seq.word) int
   if name="char seq" then 1
   else if name="typename" then 2
  else valueofencoding.encode.typename.name+2

function assignencoding(a:int, typename) int
   a+1
   