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




BT assert2(processinfo PD,BT message);




BT allocatespaceZbuiltinZint(processinfo PD,BT i) ;

BT encodewordZstdlibZintzseq(processinfo PD,BT P1);






struct str2 { BT  type;
               BT  length;
               char data[500];
               };
               

struct str2  *   stepresult( BT x);  /* defined in tau.c */
void    stepfree ( BT x); /* defined in tau.c */
void inittau(int additional); /* defined in tau.c */

struct outputformat { BT bytelength; struct bitsseq *data;};

struct bitsseq  { BT type; BT length; BT  data[50]; };



void createfilefromoutput(struct outputformat *t,int file);

struct outputformat *output(processinfo p);