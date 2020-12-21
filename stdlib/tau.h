//
//  toc.h
//  funclanguage
//
//  Created by david on 1/21/15.
//  Copyright (c) 2015 david. All rights reserved.
//


#define  BT long long int

#include <setjmp.h>
#include <pthread.h>
#include "math.h"


#define IDXUC(a,b)  (*(BT *)((a)+8*(b)))
#define  IDX(PD,P2,P1)   (*(BT*)(P2)== 0) ? IDXUC(P2,P1 + 1): ((*(BT *) (P2) )==1) ? *((unsigned char *) ((P2)+15+ (P1)  ) ) :    ((BT(*)(processinfo,BT, BT))IDXUC(P2,0))(PD,P2,P1)

typedef  struct pinfo *processinfo;

struct str2 { BT  type; BT  length; char data[500]; };  


struct bitsseq  { BT type; BT length; BT  data[50]; };



void inittau(int additional); /* defined in tau.c */
