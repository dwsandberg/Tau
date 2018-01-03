//
//  toc.h
//  funclanguage
//
//  Created by david on 1/21/15.
//  Copyright (c) 2015 david. All rights reserved.
//


#define  BT long long int

#define BRT double

#include <setjmp.h>
#include <pthread.h>
#include "math.h"


typedef  struct pinfo *processinfo;

BT PROCESS2(processinfo PD,BT pin);
BT aborted(BT p);


#define IDXUC(a,b)  (*(BT *)((a)+8*(b)))
#define  IDX(PD,P2,P1)   (*(BT*)(P2)== 0) ? IDXUC(P2,P1 + 1): ((*(BT *) (P2) )==1) ? *((unsigned char *) ((P2)+15+ (P1)  ) ) :    ((BT(*)(processinfo,BT, BT))IDXUC(P2,0))(PD,P2,P1)

//#define SETFLD3(a,x,i)       (*(BT *)((a)+8*(i))=x )

BT DECODE(processinfo PD,BT P1,BT P2);
BT ENCODE(processinfo PD,BT P1,BT P2);
BT MAPENCODE(processinfo PD,BT P2);
BT LOCALENCODE(processinfo PD,BT P2);


BT assert2(processinfo PD,BT message);


BT HASH(BT a);


BT allocatespaceZbuiltinZint(processinfo PD,BT i) ;

BT encodewordZstdlibZintzseq(processinfo PD,BT P1);


// Real Support
union cvt {BRT r;BT i;};
#define asreal(i) (((union cvt) (i)).r)
#define asint(r) (((union cvt) (r)).i)


//BT tanZbuiltinZreal(processinfo PD,BT P1);
//BT  arcsinZbuiltinZreal(processinfo PD,BT P2);
//BT  arccosZbuiltinZreal(processinfo PD,BT P3);





