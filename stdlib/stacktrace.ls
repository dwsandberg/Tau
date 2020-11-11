Module stacktrace

use mangle

use stdlib

Builtin callstack(n:int)seq.int  

Function stacktrace seq.word @(+, decodeaddress,"", callstack.30)

Builtin addresstosymbol2(a:int)seq.char  

Function addresstosymbol(a:int)word encodeword.addresstosymbol2.a

Function decodeaddress(address:int)seq.word" &br" + @(+, identity,"", codedown.addresstosymbol.address)