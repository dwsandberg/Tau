Module codegen


use codetemplates

use internalbc

use ipair.linklists2

use libdescfunc

use libscope

use llvm



use passcommon

use persistant

use seq.encoding.llvmtype

use seq.func

use seq.internalbc

use seq.libsym

use seq.libtype

use seq.linklists2

use seq.llvmconst

use seq.localmap5

use seq.seq.int

use seq.seq.seq.int

use seq.stat5


use stacktrace

use stdlib

use textio



  
function funcdec(f:inst) seq.int
 let discard=C.mangledname.f
 [ MODULECODEFUNCTION, typ.function.constantseq(nopara.f+2, i64), 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
 
 
  
use seq.seq.bits

Function codegen5(z:pass1result)seq.bits 
    PROFILE.let thename = libname(z)_1 
  let symlist = "libname initlib5 words wordlist list  profcounts profclocks profspace profrefs profstat spacecount"+ merge(thename,"$profileresult"_1)+"init22  PROCESS2 HASH"+ merge."llvm.sqrt.f64"+ merge."llvm.sin.f64"+ merge."llvm.cos.f64"
  let wordstype = array(-1, i64)
   // let conststype = array(-2, i64) //
let cxx =  conststype
 let profiletype = array(-3, i64)
        let fs=  (code.z)
      let declist=@(+,_(coding.fs),empty:seq.inst,defines.fs)
      let discard2 = @(+, C, 0,  @(+,mangledname,symlist,declist ))
      let xy=table
   let match5map=@(buildtemplates, identity, empty:seq.match5, @(+, towords, empty:seq.seq.word,coding.fs))
  // assert false report checkmap.match5map //
  let bodies=@(+,addfuncdef(match5map,coding.fs,codes.fs),empty:seq.internalbc,defines.fs)
  let profilearcs2=profilearcs
  let noprofileslots = length.profilearcs2 / 2 
   // let libsyms=@(+,tolibsym(coding.fs,codes.fs),empty:seq.libsym,defines.fs) //
    let liblib = prepareliblib2(alltypes.z,consts.last.match5map,libdesc(z ))
    let beforearcs =   value.liblib
  let arcs = place.beforearcs
  let data =   addwordseq(beforearcs,profilearcs2) 
  let x = C(array(4, i64), [ AGGREGATE, 
  C(i64, [ CONSTCECAST, 9, typ.ptr.i64, getelementptr(conststype,"list",arcs+1) ] ), 
  C(i64, [ CONSTCECAST, 9, typ.ptr.profiletype, C."profcounts"]), 
  C(i64, [ CONSTCECAST, 9, typ.ptr.profiletype, C."profclocks"]), 
  C(i64, [ CONSTCECAST, 9, typ.ptr.profiletype, C."profspace"])])
  let words = worddata 
  let worddatatype = array(length.words + 2, i64)
  let adjust = [ 0, 2 + wordcount + 1, length.a.data + 5 + 2, noprofileslots + 2 + 3]
   let libnametype = array(length.decode.thename + 1, i8)
  let libnameptr = C(ptr.i8, [ CONSTGEP, typ.libnametype, typ.ptr.libnametype, C."libname", typ.i32, C32.0, typ.i32, C32.0])
  let deflist = [ [ MODULECODEGLOBALVAR, 
  typ.libnametype, 
  2, 
  C(libnametype, [ CONSTDATA]+ decode.thename + 0)+ 1, 
  3, 
  align4, 
  0], 
  [ MODULECODEFUNCTION, 
  typ.function.[ i64, ptr.i8, ptr.i64, ptr.i64, ptr.i64,  ptr.i64], 
  0, 
  1, 
  0, 
  1, 
  0, 
  0, 
  0, 
  0, 
  0, 
  0, 
  0, 
  0], 
  [ MODULECODEGLOBALVAR, typ.wordstype, 2, C(wordstype, [ CONSTNULL])+ 1, 3, align8 + 1, 0], 
  [ MODULECODEGLOBALVAR, 
  typ.worddatatype, 
  2, 
  1 + C(worddatatype, [ AGGREGATE, C64.0, C64.length.words]+ words), 
  3, 
  align8 + 1, 
  0], 
  [ MODULECODEGLOBALVAR, typ.conststype, 2, initializer(conststype, data), 3, align8 + 1, 0], 
  // profcounts // 
   [ MODULECODEGLOBALVAR, typ.profiletype, 2, C(profiletype, [ CONSTNULL])+ 1, 3, align8 + 1, 0], 
  // profclocks // 
   [ MODULECODEGLOBALVAR, typ.profiletype, 2, C(profiletype, [ CONSTNULL])+ 1, 3, align8 + 1, 0], 
  // profspace // 
   [ MODULECODEGLOBALVAR, typ.profiletype, 2, C(profiletype, [ CONSTNULL])+ 1, 3, align8 + 1, 0], 
  // profrefs // 
   [ MODULECODEGLOBALVAR, typ.profiletype, 2, C(profiletype, [ CONSTNULL])+ 1, 3, align8 + 1, 0], 
  // profstat // [ MODULECODEGLOBALVAR, typ.array(4, i64), 2, x + 1, 3, align8 + 1, 0], 
  // spacecount // [ MODULECODEGLOBALVAR, typ.i64, 2, 0, 0, align8 + 1, 0], 
   // profileresult // [ MODULECODEFUNCTION, typ.function.[ i64], 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], 
  // init22 // [ MODULECODEFUNCTION, typ.function.[ VOID], 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], 
   // PROCESS2 // [ MODULECODEFUNCTION, typ.function.[ i64, i64, i64], 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], 
  // hash // [ MODULECODEFUNCTION, typ.function.[ i64, i64], 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], 
  // llvm.sqrt.f64 // 
   [ MODULECODEFUNCTION, typ.function.[ double, double], 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], 
  // llvm.sin.f64 // 
   [ MODULECODEFUNCTION, typ.function.[ double, double], 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], 
  // llvm.cos.f64 // 
   [ MODULECODEFUNCTION, typ.function.[ double, double], 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]]
   +    @(+, funcdec,empty:seq.seq.int, declist) 
  let bodytxts = [ BLOCKCOUNT(1, 1)+ RET(1, C(i64, [ CONSTCECAST, 9, typ.ptr.array(4, i64), C."profstat"])), 
  BLOCKCOUNT(1, 1)+ 
  CALL(1, 0, 32768, typ.function.[ i64, ptr.i8, ptr.i64, ptr.i64, ptr.i64,  ptr.i64], 
   C."initlib5"  , libnameptr, 
  getelementptr(wordstype,"words",0), 
  getelementptr(worddatatype,"wordlist",0),
   getelementptr(conststype,"list",0), 
    getelementptr(conststype,"list",index.liblib+1) )
   + GEP(2, 1, typ.profiletype, C."profclocks", C64.0, C64.1)
  + STORE(3, -2, C64.noprofileslots, align8, 0)+ GEP(3, 1, typ.profiletype, C."profspace", C64.0, C64.1)
  + STORE(4, -3, C64.noprofileslots, align8, 0)+ GEP(4, 1, typ.profiletype, C."profcounts", C64.0, C64.1)
  + STORE(5, -4, C64.noprofileslots, align8, 0)+ GEP(5, 1, typ.profiletype, C."profrefs", C64.0, C64.1)
  + STORE(6, -5, C64.noprofileslots, align8, 0)+ RET.6]+ bodies 
   llvm(deflist, bodytxts, adjust(typerecords, adjust, 1)
  )


  
use altgen


use codetemplates

use seq.match5

use seq.inst


 







  



