Module test20

use standard

use seq.int

use seq.q

type p is a:int, b:int, c:int

type q is d:int, e:p, f:int

Export p(a:int, b:int, c:int)p export

Export q(a:int, b:p, c:int)q export

function z q q(1, p(2, 3, 4), 5)

function f2 seq.int[d.z, a.e.z, b.e.z, c.e.z, f.z]

Function test20 boolean f2 = [1, 2, 3, 4, 5]

Function c11 seq.q[q(4, p(1, 2, 3), 5), q(41, p(11, 21, 31), 51)] 