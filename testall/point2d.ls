Module point2d

The following paragraph starts a type definition which is immediately followed by a paragraph that defines the compoents of the type.The struct paragraph must immediate follow the type paragraph but does not need to be present as a type is simply a set of functions.

type point2d is record x:int, y:int

The follow paragraph that begins with use allows reference to functions defined in another type.In this case, the standard build it funcitons.

use stdlib

use seq.word

The follow three paragraphs all access to the function automaticaly defined by the struct defintion in other types that “use” this package.If these paragraphs are omitted the functions would not be available outside of this type.

Function point2d(a:int, b:int)point2d export

Function y(a:point2d)int export

Function x(a:point2d)int export

The following two paragraphs defines an addition and subtraction operator on points.

Function +(a:point2d, b:point2d)point2d point2d(x.a + x.b, y.a + y.b)

Function-(a:point2d, b:point2d)point2d point2d(x.a - x.b, y.a - y.b)

Function print(p:point2d)seq.word 
 {"("+ toword.x.p +","+ toword.y.p +")"}

The beginning of the next paragraphs ends the point type.

