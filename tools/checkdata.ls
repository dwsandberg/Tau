#!/usr/local/bin/tau checkdata2 checkdata2

Library checkdata checkdata2 checkdataio
uses stdlib
exports checkdata checkdata2 checkdataio

module checkdata

run checkdata convert

use seq.UTF8

use UTF8

use seq.char

use checkdataio

use real

use seq.rec

use stdlib

use words

/Function countx int @(+, toint, 0, decodeword."XXXX"_1)

Function archivedrecs seq.rec getcheckdata

Export type:rec

type rec is record checkno:int, payee:seq.word, amount:real, deposit:real, clear:seq.word, group:seq.word

Export rec(checkno:int, payee:seq.word, amount:real, deposit:real, clear:seq.word, group:seq.word)rec

/function =(a:rec, b:rec)boolean checkno.a = checkno.b &and payee.a = payee.b &and amount.a = amount.b &and deposit.a = deposit.b &and clear.a = clear.b &and group.a = group.b

Export checkno(rec)int

Export payee(rec)seq.word

Export amount(rec)real

Export deposit(rec)real

Export clear(rec)seq.word

Export group(rec)seq.word

Function printcsv(a:rec)seq.word
 [ encodeword.[ char.10], toword.checkno.a] + "," + payee.a + ","
 + print(2, amount.a)
 + ","
 + print(2, deposit.a)
 + ","
 + clear.a
 + ","
 + group.a

Function print(a:seq.rec)seq.word @(+, print,"", a)

Function print(a:rec)seq.word
 " &br, rec(" + toword.checkno.a + ',"' + payee.a
 + '", '
 + print(2, amount.a)
 + ","
 + print(2, deposit.a)
 + ',"'
 + clear.a
 + '","'
 + group.a
 + '")'

Function printhtml(a:rec)seq.word
 " &br  &row" + toword.checkno.a + " &cell" + subseq(payee.a, 1, 10)
 + " &cell"
 + print(2, amount.a)
 + " &cell"
 + print(2, deposit.a)
 + " &cell"
 + clear.a
 + " &cell"
 + group.a

Function printhtml(a:seq.rec)seq.word
 " &{ table summary  &row checkno  &cell payee  &cell amount  &cell deposit  &cell clear  &cell group" + @(+, printhtml,"", a)
 + " &}"

"<table><tr><th> checkno.<th> payee <th> amount <th> deposit <th> clear <th> group"+ @(+, printhtml,"", a)+"</table>"