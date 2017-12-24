Module stacktrace

use libscope

use stdlib

Function callstack(n:int)seq.int builtin.usemangle

Function stacktrace seq.word @(+, decodeaddress,"", callstack.30)

function addresstosymbol2(a:int)seq.int builtin.usemangle

Function addresstosymbol(a:int)word encodeword.addresstosymbol2.a

Function decodeaddress(address:int)seq.word 
 {"<BR>"+ @(+, identity,"", codedown.addresstosymbol.address)}

