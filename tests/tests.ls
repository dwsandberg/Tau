Module tests

Library tests bug7 checking myseq point randomphrase test11 test20 testencoding testfileio testmodules testprocess 
testsCompile/test11a testsCompile/testall 
testsCompile/testopt testseq   wordfreq tree uses stdlib exports tests

use UTF8

use format

use standard

use testall

use seq.char

use seq.word

use seq.seq.word

use bits

use real

Export -(real) real

Export <<(bits, int)bits

Export xor(bits, bits)bits

Export ∨(bits, bits)bits 

Function entrypoint(s:UTF8)UTF8
let args = towords.s
let arg = [first.args]
let arg2 = if length.args > 1 then[args_2]else""
HTMLformat.if arg = "testall"then testall else"unknown arg" + args 