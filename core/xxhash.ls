Module xxhash

use bits

use standard

Function rotateleft(x:bits, n:int) bits x << n ∨ x >> (64 - n)

Function hash(acc:bits, x:int) bits
{after xxhash
/br example use to hash x and y finalmix (hash (hash (hashstart (seed), x), y))}
let PRIME1 = 11400714785074694791
let PRIME2 = 14029467366897019727
let PRIME4 = 9650029242287828579,
bits(
 toint.rotateleft(acc ⊻ bits(toint.rotateleft(bits(toint.acc + x * PRIME2), 31) * PRIME1), 27)
  * PRIME1
  + PRIME4
)

Function hashstart(seed:int) bits
let PRIME5 = 2870177450012600261,
bits(seed + PRIME5 + 64)

Function hashstart bits hashstart.0

Function finalmix(acc:bits) int
let PRIME2 = 14029467366897019727
let PRIME3 = 1609587929392839161
let acc1 = bits(toint(acc ⊻ acc >> 33) * PRIME2)
let acc2 = bits(toint(acc1 ⊻ acc1 >> 29) * PRIME3),
abs.toint(acc2 ⊻ acc2 >> 32)

Function rotl32(x:bits, n:int) bits 0xFFFF FFFF ∧ (x << n ∨ x >> (32 - n))

Function hash32(hash:bits, key:int) bits
rotl32(bits(toint.hash + toint(bits.2246822519 * key)), 13) * 2654435761

Function *(a:bits, b:int) bits
let m = toint(bits.b ∨ bits.0)
let nlo = toint(a ∧ 0xFFFF)
let nhi = toint(a ∧ 0xFFFF << 16),
bits(toint(bits(nhi * m) ∧ 0xFFFF FFFF) + nlo * m) ∧ 0xFFFF FFFF

Function finalmix32(hash:bits) int
let h32c = (hash ⊻ hash >> 15) * 668265263
let h32d = (h32c ⊻ h32c >> 13) * 374761393,
abs.toint((h32d ⊻ h32d >> 16) ∧ 0xFFFF FFFF)

Function hashstart32(seed:int) bits let PRIME5 = 374761393, bits(seed + PRIME5) 