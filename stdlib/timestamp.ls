Module timestamp

use UTF8

use bits

use standard

use seq.byte

Export type:timestamp

type timestamp is toint:int

function subseq(a:UTF8, i:int, j:int)UTF8 UTF8.subseq(toseqbyte.a, i, j)

Function testjulian boolean
[ tojulian(2000, 1, 1)
, tojulian(1999, 1, 1)
, tojulian(1987, 1, 27)
, tojulian(1987, 6, 19)
, tojulian(1988, 1, 27)
, tojulian(1988, 6, 19)
, tojulian(1900, 1, 1)
, tojulian(1600, 1, 1)
, tojulian(1600, 12, 31)
]
= [ 2451544, 2451179, 2446822, 2446965, 2447187, 2447331, 2415020, 2305447, 2305812]

Function tojulian(year:int, month:int, day:int)int
let ayear = if month > 2 then year else year - 1
let amonth = if month > 2 then month else month + 12 /if
(amonth + 1) * 306001 / 10000 + day + 1720994 + 2 - ayear / 100 + ayear / 100 / 4 + 1461 * ayear / 4

Function dayofyear(t:timestamp)int
toint.t / (24 * 60 * 60) - tojulian((fromJuliantointseq(toint.t / (24 * 60 * 60)))_1, 1, 1) + 1

Function fromJuliantointseq(dt:int)seq.int
let a =((dt + 1) * 4 - 7468865) / 146097
let b = dt + 1 + 1 + a - a / 4 + 1524
let c =(b * 20 - 2442) / 7305
let d = b - 1461 * c / 4
let e = d * 10000 / 306001
let m = e - if e > 13 then 13 else 1
[ c - if m > 2 then 4716 else 4715, m, d - e * 306001 / 10000]

Function timestamplit(t:UTF8)timestamp
{ assumes t is in format 2019-12-12T12:48:11 }
let year = intlit.subseq(t, 1, 4)
let month = intlit.subseq(t, 6, 7)
let day = intlit.subseq(t, 9, 10)
let hour = intlit.subseq(t, 12, 13)
let minutes = intlit.subseq(t, 15, 16)
let second = intlit.subseq(t, 18, 19)
let date = tojulian(year, month, day)
timestamp(((date * 24 + hour) * 60 + minutes) * 60 + second)

Function totimestamp(year:int, month:int, day:int, hour:int, minute:int, second:int)timestamp
timestamp(((tojulian(year, month, day) * 24 + hour) * 60 + minute) * 60 + second)

Function decompose(ts:timestamp)seq.int
{ returns sequence of year, month, day, hour, minute, second }
let t = toint.ts
let a = t mod (24 * 60 * 60)
let seconds = a mod 60
let minutes = a / 60 mod 60
let hours = a / 3600
fromJuliantointseq(t / (24 * 60 * 60)) + [ hours, minutes, seconds]

Function print(ts:timestamp)seq.word
let d = decompose.ts
[ merge.[ toword.d_1,"-"_1, toword.d_2,"-"_1, toword.d_3
,"."_1, toword.d_4,":"_1, toword.d_5,":"_1
, toword.d_6]
]

Builtin currenttime timestamp

Function asseconds(t:timestamp)int toint.t

Function totimestamp(seconds:int)timestamp timestamp.seconds 