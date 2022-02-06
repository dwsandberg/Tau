
#include <setjmp.h>
#include <pthread.h>
#include <stdio.h>


#define  BT long long int
typedef  struct pinfo *processinfo;

struct spaceinfo { char * nextone,*lastone; BT *blocklist; };


pthread_mutex_t sharedspace_mutex;

struct pinfo { BT aborted; // 1 if aborted
    BT message; // message if aborted (seq.word)
    BT result;  // result returned by process
    BT joined;  // has process been joined to parent?
    struct spaceinfo space; //for space allocation
    jmp_buf env;
    BT error;
    pthread_t pid;
    struct einfo **encodings;
    processinfo spawningprocess;
    BT profileindex;
    BT (*finishprof)(BT idx,BT x);
    BT freespace;
    BT newencodings;
     // info needed to create thread
    BT  deepcopyresult;
    BT  deepcopyseqword;
    BT func;
    BT argtype;
    // argtype is the follow sequence of bits from high to low:
    //    1
    //  for each argument of func 1 if is  double else 0 
    //   1 if return type is double else 0
    // This is needed because function calling convention may differ when a double is used as
    // a parameter or result type
    BT *args;
               };

void threadbody(struct pinfo *q);

void myfree(struct spaceinfo *sp);

BT allocatespace(processinfo PD, BT i);

void assertexit(int b,char *message);

void initprocessinfo(processinfo p,processinfo PD);

BT createthread(processinfo PD ,BT  deepcopyresult  ,BT  deepcopyseqword  ,BT func,BT * args,BT argtype );