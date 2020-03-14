Module xxhash

use bits

use stdlib

Function rotateleft(x:bits, n:int)bits x << n ∨ x >> 64 - n

Function hash(acc:bits, x:int)bits
 // after xxhash //
 // example use to hash x and y finalmix(hash(hash(hashstart(seed), x), y))//
 let PRIME1 = 11400714785074694791
 let PRIME2 = 14029467366897019727
 let PRIME4 = 9650029242287828579
  bits(toint
  .rotateleft(xor(acc, bits(toint.rotateleft(bits(toint.acc + x * PRIME2), 31) * PRIME1)), 27)
  * PRIME1
  + PRIME4)

Function hashstart(seed:int)bits
 let PRIME5 = 2870177450012600261
  bits(seed + PRIME5 + 64)

Function hashstart bits hashstart.0

Function finalmix(acc:bits)int
 let PRIME2 = 14029467366897019727
 let PRIME3 = 1609587929392839161
 let acc1 = bits(toint.xor(acc, acc >> 33) * PRIME2)
 let acc2 = bits(toint.xor(acc1, acc1 >> 29) * PRIME3)
  abs.toint.xor(acc2, acc2 >> 32)