//
//  toc.h
//  funclanguage
//
//  Created by david on 1/21/15.
//  Copyright (c) 2015 david. All rights reserved.
//

//#define BT int

#define  BT long long int
//#define  BRT float
#define BRT double

#include <setjmp.h>
#include <pthread.h>
#include "math.h"


typedef  struct pinfo *processinfo;

BT PROCESS2(processinfo PD,BT pin);
BT aborted(BT p);

#define EQL(a,b)((a)==(b))
#define ADD(a,b) ((a)+(b))
#define Q2AZbuiltinZintZint(a,b) ((a)*(b))
#define Q2BZbuiltinZintZint(a,b) ((a)+(b))
#define Q3DZbuiltinZintZint(a,b) ((a)==(b))
#define Q2DZbuiltinZintZint(a,b) ((a)-(b))
#define Q2FZbuiltinZintZint(a,b) ((a)/(b))
#define Q3FZbuiltinZintZint(a,b) ((a)>(b)?2:(a)==(b)?1:0)
#define Q3EZbuiltinZintZint(a,b) ((a)>(b))
#define Q2BZbuiltinZTzaddressZint(a,b) ((a)+((b)<<3))


#define IDXUC(a,b)  (*(BT *)((a)+8*(b)))
#define  IDX(PD,P2,P1)   (*(BT*)(P2)== 0) ? IDXUC(P2,P1 + 1): ((*(BT *) (P2) )==1) ? *((unsigned char *) ((P2)+15+ (P1)  ) ) :    ((BT(*)(processinfo,BT, BT))IDXUC(P2,0))(PD,P2,P1)
#define notZbuiltinZboolean(a)   (((a)+1)&1)                            

#define SETFLD3(a,x,i)       (*(BT *)((a)+8*(i))=x )
#define SETFLDBYTE(PD,a,x,i) (*(char *)((a)+(i)+15)=IDX(PD,x,i))

BT DECODE(processinfo PD,BT P1,BT P2);
BT ENCODE(processinfo PD,BT P1,BT P2);
BT MAPENCODE(processinfo PD,BT P2);
BT LOCALENCODE(processinfo PD,BT P2);


BT assert2(processinfo PD,BT message);

#define hashZbuiltinZint(a)  HASH(a) 

BT HASH(BT a);


BT allocatespaceZbuiltinZint(processinfo PD,BT i) ;

BT encodewordZstdlibZintzseq(processinfo PD,BT P1);


// Real Support
union cvt {BRT r;BT i;};
#define asreal(i) (((union cvt) (i)).r)
#define asint(r) (((union cvt) (r)).i)

#define intpartZbuiltinZreal(a)   ((BT)(asreal(a)))
#define int2realZbuiltinZint(a)  asint((BRT)(a)) 
#define Q3FZbuiltinZrealZreal(a,b) (asreal(a)>asreal(b)?2:asreal(a)==asreal(b)?1:0)
#define Q2BZbuiltinZrealZreal(a,b) asint(asreal(a)+asreal(b))
#define Q2DZbuiltinZrealZreal(a,b) asint(asreal(a)-asreal(b))
#define Q2AZbuiltinZrealZreal(a,b) asint(asreal(a)*asreal(b))
#define Q2FZbuiltinZrealZreal(a,b) asint(asreal(a)/asreal(b))
#define sqrtZbuiltinZreal(a)  asint(sqrt(asreal(a)))
#define cosZbuiltinZreal( a)  asint(cos(asreal(a)))
#define sinZbuiltinZreal( a)  asint(sin(asreal(a)))
// #define tanZbuiltinZreal( a)  asint(tan(asreal(a)))
// #define arcsinZbuiltinZreal( a)  asint(asin(asreal(a)))
// #define arccosZbuiltinZreal(a)  asint(acos(asreal(a)))

BT tanZbuiltinZreal(processinfo PD,BT P1);
BT  arcsinZbuiltinZreal(processinfo PD,BT P2);
BT  arccosZbuiltinZreal(processinfo PD,BT P3);





