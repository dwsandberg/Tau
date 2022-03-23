
#include "tau.h"

// Real Support
union cvt {double r;BT i;};
#define asreal(i) (((union cvt) (i)).r)
#define asint(r) (((union cvt) (r)).i)

void initprocessinfo(processinfo p,processinfo PD){
    p->aborted = -1;
    p->message =&(p->zero);
    p->messageUTF8 =&(p->zero);
    p->body2 =&(p->zero) ;
    p->body = &(p->seqtype) ;
    p->spawningprocess =PD;
    p->encodings = PD->encodings;
    p->pid = pthread_self ();
     p->zero = 0;
    p->seqtype=0;
    p->seqlength=1;
    p->space.nextone =0;
    p->space.lastone =0;
    p->space.blocklist = 0;
    p->error =0;
    p->profileindex = 0;
    p->freespace=1;
    p->newencodings=0;
}


BT createthread(processinfo PD ,BT  deepcopyresult  ,BT  deepcopyseqword  ,BT func,BT * args,BT argtype ){
BT profileidx=0;
BT (*finishprof)(BT idx,BT x) =NULL;
  pthread_attr_t 	stackSizeAttribute;
  size_t			stackSize = 0;
  pthread_attr_init (&stackSizeAttribute);
  pthread_attr_setstacksize (&stackSizeAttribute, 1024 * 1024 * 12 *8 );
  pthread_attr_getstacksize(&stackSizeAttribute, &stackSize); 
  /*  fprintf(stderr,"Stack size %d\n", stackSize);*/
  processinfo p=(processinfo)  allocatespace(PD,(sizeof (struct pinfo)+7)/8);
  initprocessinfo(p,PD);
  p->deepcopyresult =  deepcopyresult; 
    p->deepcopyseqword =  deepcopyseqword;
    p->func= func;
    p->argtype=argtype;
     p->args= args;

  p->profileindex = profileidx; 
  p->finishprof=finishprof;
  assertexit(0==pthread_create(&p->pid, &stackSizeAttribute, (void *(*)(void *) )threadbody,(void *) p),"ERROR");
  return (BT)p;
} 

BT createthreadI(processinfo PD ,BT  deepcopyresult  ,BT  deepcopyseqword  ,BT func,BT * args,BT argtype ){
return createthread(PD,   deepcopyresult  ,  deepcopyseqword  , func,  args+2, argtype);}


/*

The following code  was used to generate case in the threadbody.

Function test14 seq.word 
    arithseq(16,1,2)  @ list("",EOL,thecase(@e))

function tobitseq( s:seq.boolean, i:int ) seq.boolean if i=1 then empty:seq.boolean
  else    tobitseq(s, i / 2 ) +  if i mod 2 =0 then false else true
 
function thecase(i:int) seq.word
   let paras=tobitseq (empty:seq.boolean, i)
   let arglist= paras >> 1 @+("))(q->func) )(q", if @e then ",asreal(q->args["+print(@i-1)+"])"  else ",q->args["+print(@i-1)+"]" )
   let argtyps= paras >> 1 @+("", if @e then ",double"  else ",BT" ) 
   "case"+print.i+": result="+   if last.paras then 
        "asint(((double (*) (processinfo"+argtyps+arglist+ ")); break;" 
   else  
       "((BT (*) (processinfo"+argtyps+arglist+"); break;"

 */

  

void threadbody(struct pinfo *q){
if (setjmp(q->env)!=0) {
       q->message= ((BT *(*) (processinfo,BT))(q->deepcopyseqword) ) (q->spawningprocess,q->error);
        q->aborted = 1;}
    else {BT result;
     // fprintf(stderr,"start threadbody\n");
    
       //  fprintf(stderr,"case %lld \n",q->argtype);
      switch( q->argtype  ){
case 2:result =((BT(*)(processinfo))(q->func))(q); break; 
case 3:result = asint(((double(*)(processinfo))(q->func))(q)); break; 
case 4:result =((BT(*)(processinfo, BT))(q->func))(q, q->args [ 0]); break; 
case 5:result = asint(((double(*)(processinfo, BT))(q->func))(q, q->args [ 0])); break; 
case 6:result =((BT(*)(processinfo, double))(q->func))(q, asreal(q->args [ 0])); break; 
case 7:result = asint(((double(*)(processinfo, double))(q->func))(q, asreal(q->args [ 0]))); break; 
case 8:result =((BT(*)(processinfo, BT, BT))(q->func))(q, q->args [ 0], q->args [ 1]); break; 
case 9:result = asint(((double(*)(processinfo, BT, BT))(q->func))(q, q->args [ 0], q->args [ 1])); break; 
case 10:result =((BT(*)(processinfo, BT, double))(q->func))(q, q->args [ 0], asreal(q->args [ 1])); break; 
case 11:result = asint(((double(*)(processinfo, BT, double))(q->func))(q, q->args [ 0], asreal(q->args [ 1]))); break; 
case 12:result =((BT(*)(processinfo, double, BT))(q->func))(q, asreal(q->args [ 0]), q->args [ 1]); break; 
case 13:result = asint(((double(*)(processinfo, double, BT))(q->func))(q, asreal(q->args [ 0]), q->args [ 1])); break; 
case 14:result =((BT(*)(processinfo, double, double))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1])); break; 
case 15:result = asint(((double(*)(processinfo, double, double))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]))); break; 
case 16:result =((BT(*)(processinfo, BT, BT, BT))(q->func))(q, q->args [ 0], q->args [ 1], q->args [ 2]); break; 
case 17:result = asint(((double(*)(processinfo, BT, BT, BT))(q->func))(q, q->args [ 0], q->args [ 1], q->args [ 2])); break; 
case 18:result =((BT(*)(processinfo, BT, BT, double))(q->func))(q, q->args [ 0], q->args [ 1], asreal(q->args [ 2])); break; 
case 19:result = asint(((double(*)(processinfo, BT, BT, double))(q->func))(q, q->args [ 0], q->args [ 1], asreal(q->args [ 2]))); break; 
case 20:result =((BT(*)(processinfo, BT, double, BT))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), q->args [ 2]); break; 
case 21:result = asint(((double(*)(processinfo, BT, double, BT))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), q->args [ 2])); break; 
case 22:result =((BT(*)(processinfo, BT, double, double))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), asreal(q->args [ 2])); break; 
case 23:result = asint(((double(*)(processinfo, BT, double, double))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), asreal(q->args [ 2]))); break; 
case 24:result =((BT(*)(processinfo, double, BT, BT))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], q->args [ 2]); break; 
case 25:result = asint(((double(*)(processinfo, double, BT, BT))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], q->args [ 2])); break; 
case 26:result =((BT(*)(processinfo, double, BT, double))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], asreal(q->args [ 2])); break; 
case 27:result = asint(((double(*)(processinfo, double, BT, double))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], asreal(q->args [ 2]))); break; 
case 28:result =((BT(*)(processinfo, double, double, BT))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), q->args [ 2]); break; 
case 29:result = asint(((double(*)(processinfo, double, double, BT))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), q->args [ 2])); break; 
case 30:result =((BT(*)(processinfo, double, double, double))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), asreal(q->args [ 2])); break; 
case 31:result = asint(((double(*)(processinfo, double, double, double))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), asreal(q->args [ 2]))); break; 
case 32:result =((BT(*)(processinfo, BT, BT, BT, BT))(q->func))(q, q->args [ 0], q->args [ 1], q->args [ 2], q->args [ 3]); break; 
case 33:result = asint(((double(*)(processinfo, BT, BT, BT, BT))(q->func))(q, q->args [ 0], q->args [ 1], q->args [ 2], q->args [ 3])); break; 
case 34:result =((BT(*)(processinfo, BT, BT, BT, double))(q->func))(q, q->args [ 0], q->args [ 1], q->args [ 2], asreal(q->args [ 3])); break; 
case 35:result = asint(((double(*)(processinfo, BT, BT, BT, double))(q->func))(q, q->args [ 0], q->args [ 1], q->args [ 2], asreal(q->args [ 3]))); break; 
case 36:result =((BT(*)(processinfo, BT, BT, double, BT))(q->func))(q, q->args [ 0], q->args [ 1], asreal(q->args [ 2]), q->args [ 3]); break; 
case 37:result = asint(((double(*)(processinfo, BT, BT, double, BT))(q->func))(q, q->args [ 0], q->args [ 1], asreal(q->args [ 2]), q->args [ 3])); break; 
case 38:result =((BT(*)(processinfo, BT, BT, double, double))(q->func))(q, q->args [ 0], q->args [ 1], asreal(q->args [ 2]), asreal(q->args [ 3])); break; 
case 39:result = asint(((double(*)(processinfo, BT, BT, double, double))(q->func))(q, q->args [ 0], q->args [ 1], asreal(q->args [ 2]), asreal(q->args [ 3]))); break; 
case 40:result =((BT(*)(processinfo, BT, double, BT, BT))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), q->args [ 2], q->args [ 3]); break; 
case 41:result = asint(((double(*)(processinfo, BT, double, BT, BT))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), q->args [ 2], q->args [ 3])); break; 
case 42:result =((BT(*)(processinfo, BT, double, BT, double))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), q->args [ 2], asreal(q->args [ 3])); break; 
case 43:result = asint(((double(*)(processinfo, BT, double, BT, double))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), q->args [ 2], asreal(q->args [ 3]))); break; 
case 44:result =((BT(*)(processinfo, BT, double, double, BT))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), asreal(q->args [ 2]), q->args [ 3]); break; 
case 45:result = asint(((double(*)(processinfo, BT, double, double, BT))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), asreal(q->args [ 2]), q->args [ 3])); break; 
case 46:result =((BT(*)(processinfo, BT, double, double, double))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), asreal(q->args [ 2]), asreal(q->args [ 3])); break; 
case 47:result = asint(((double(*)(processinfo, BT, double, double, double))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), asreal(q->args [ 2]), asreal(q->args [ 3]))); break; 
case 48:result =((BT(*)(processinfo, double, BT, BT, BT))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], q->args [ 2], q->args [ 3]); break; 
case 49:result = asint(((double(*)(processinfo, double, BT, BT, BT))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], q->args [ 2], q->args [ 3])); break; 
case 50:result =((BT(*)(processinfo, double, BT, BT, double))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], q->args [ 2], asreal(q->args [ 3])); break; 
case 51:result = asint(((double(*)(processinfo, double, BT, BT, double))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], q->args [ 2], asreal(q->args [ 3]))); break; 
case 52:result =((BT(*)(processinfo, double, BT, double, BT))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], asreal(q->args [ 2]), q->args [ 3]); break; 
case 53:result = asint(((double(*)(processinfo, double, BT, double, BT))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], asreal(q->args [ 2]), q->args [ 3])); break; 
case 54:result =((BT(*)(processinfo, double, BT, double, double))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], asreal(q->args [ 2]), asreal(q->args [ 3])); break; 
case 55:result = asint(((double(*)(processinfo, double, BT, double, double))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], asreal(q->args [ 2]), asreal(q->args [ 3]))); break; 
case 56:result =((BT(*)(processinfo, double, double, BT, BT))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), q->args [ 2], q->args [ 3]); break; 
case 57:result = asint(((double(*)(processinfo, double, double, BT, BT))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), q->args [ 2], q->args [ 3])); break; 
case 58:result =((BT(*)(processinfo, double, double, BT, double))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), q->args [ 2], asreal(q->args [ 3])); break; 
case 59:result = asint(((double(*)(processinfo, double, double, BT, double))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), q->args [ 2], asreal(q->args [ 3]))); break; 
case 60:result =((BT(*)(processinfo, double, double, double, BT))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), asreal(q->args [ 2]), q->args [ 3]); break; 
case 61:result = asint(((double(*)(processinfo, double, double, double, BT))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), asreal(q->args [ 2]), q->args [ 3])); break; 
case 62:result =((BT(*)(processinfo, double, double, double, double))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), asreal(q->args [ 2]), asreal(q->args [ 3])); break; 
case 63:result = asint(((double(*)(processinfo, double, double, double, double))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), asreal(q->args [ 2]), asreal(q->args [ 3]))); break; 
case 64:result =((BT(*)(processinfo, BT, BT, BT, BT, BT))(q->func))(q, q->args [ 0], q->args [ 1], q->args [ 2], q->args [ 3], q->args [ 4]); break; 
case 65:result = asint(((double(*)(processinfo, BT, BT, BT, BT, BT))(q->func))(q, q->args [ 0], q->args [ 1], q->args [ 2], q->args [ 3], q->args [ 4])); break; 
case 66:result =((BT(*)(processinfo, BT, BT, BT, BT, double))(q->func))(q, q->args [ 0], q->args [ 1], q->args [ 2], q->args [ 3], asreal(q->args [ 4])); break; 
case 67:result = asint(((double(*)(processinfo, BT, BT, BT, BT, double))(q->func))(q, q->args [ 0], q->args [ 1], q->args [ 2], q->args [ 3], asreal(q->args [ 4]))); break; 
case 68:result =((BT(*)(processinfo, BT, BT, BT, double, BT))(q->func))(q, q->args [ 0], q->args [ 1], q->args [ 2], asreal(q->args [ 3]), q->args [ 4]); break; 
case 69:result = asint(((double(*)(processinfo, BT, BT, BT, double, BT))(q->func))(q, q->args [ 0], q->args [ 1], q->args [ 2], asreal(q->args [ 3]), q->args [ 4])); break; 
case 70:result =((BT(*)(processinfo, BT, BT, BT, double, double))(q->func))(q, q->args [ 0], q->args [ 1], q->args [ 2], asreal(q->args [ 3]), asreal(q->args [ 4])); break; 
case 71:result = asint(((double(*)(processinfo, BT, BT, BT, double, double))(q->func))(q, q->args [ 0], q->args [ 1], q->args [ 2], asreal(q->args [ 3]), asreal(q->args [ 4]))); break; 
case 72:result =((BT(*)(processinfo, BT, BT, double, BT, BT))(q->func))(q, q->args [ 0], q->args [ 1], asreal(q->args [ 2]), q->args [ 3], q->args [ 4]); break; 
case 73:result = asint(((double(*)(processinfo, BT, BT, double, BT, BT))(q->func))(q, q->args [ 0], q->args [ 1], asreal(q->args [ 2]), q->args [ 3], q->args [ 4])); break; 
case 74:result =((BT(*)(processinfo, BT, BT, double, BT, double))(q->func))(q, q->args [ 0], q->args [ 1], asreal(q->args [ 2]), q->args [ 3], asreal(q->args [ 4])); break; 
case 75:result = asint(((double(*)(processinfo, BT, BT, double, BT, double))(q->func))(q, q->args [ 0], q->args [ 1], asreal(q->args [ 2]), q->args [ 3], asreal(q->args [ 4]))); break; 
case 76:result =((BT(*)(processinfo, BT, BT, double, double, BT))(q->func))(q, q->args [ 0], q->args [ 1], asreal(q->args [ 2]), asreal(q->args [ 3]), q->args [ 4]); break; 
case 77:result = asint(((double(*)(processinfo, BT, BT, double, double, BT))(q->func))(q, q->args [ 0], q->args [ 1], asreal(q->args [ 2]), asreal(q->args [ 3]), q->args [ 4])); break; 
case 78:result =((BT(*)(processinfo, BT, BT, double, double, double))(q->func))(q, q->args [ 0], q->args [ 1], asreal(q->args [ 2]), asreal(q->args [ 3]), asreal(q->args [ 4])); break; 
case 79:result = asint(((double(*)(processinfo, BT, BT, double, double, double))(q->func))(q, q->args [ 0], q->args [ 1], asreal(q->args [ 2]), asreal(q->args [ 3]), asreal(q->args [ 4]))); break; 
case 80:result =((BT(*)(processinfo, BT, double, BT, BT, BT))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), q->args [ 2], q->args [ 3], q->args [ 4]); break; 
case 81:result = asint(((double(*)(processinfo, BT, double, BT, BT, BT))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), q->args [ 2], q->args [ 3], q->args [ 4])); break; 
case 82:result =((BT(*)(processinfo, BT, double, BT, BT, double))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), q->args [ 2], q->args [ 3], asreal(q->args [ 4])); break; 
case 83:result = asint(((double(*)(processinfo, BT, double, BT, BT, double))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), q->args [ 2], q->args [ 3], asreal(q->args [ 4]))); break; 
case 84:result =((BT(*)(processinfo, BT, double, BT, double, BT))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), q->args [ 2], asreal(q->args [ 3]), q->args [ 4]); break; 
case 85:result = asint(((double(*)(processinfo, BT, double, BT, double, BT))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), q->args [ 2], asreal(q->args [ 3]), q->args [ 4])); break; 
case 86:result =((BT(*)(processinfo, BT, double, BT, double, double))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), q->args [ 2], asreal(q->args [ 3]), asreal(q->args [ 4])); break; 
case 87:result = asint(((double(*)(processinfo, BT, double, BT, double, double))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), q->args [ 2], asreal(q->args [ 3]), asreal(q->args [ 4]))); break; 
case 88:result =((BT(*)(processinfo, BT, double, double, BT, BT))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), asreal(q->args [ 2]), q->args [ 3], q->args [ 4]); break; 
case 89:result = asint(((double(*)(processinfo, BT, double, double, BT, BT))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), asreal(q->args [ 2]), q->args [ 3], q->args [ 4])); break; 
case 90:result =((BT(*)(processinfo, BT, double, double, BT, double))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), asreal(q->args [ 2]), q->args [ 3], asreal(q->args [ 4])); break; 
case 91:result = asint(((double(*)(processinfo, BT, double, double, BT, double))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), asreal(q->args [ 2]), q->args [ 3], asreal(q->args [ 4]))); break; 
case 92:result =((BT(*)(processinfo, BT, double, double, double, BT))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), asreal(q->args [ 2]), asreal(q->args [ 3]), q->args [ 4]); break; 
case 93:result = asint(((double(*)(processinfo, BT, double, double, double, BT))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), asreal(q->args [ 2]), asreal(q->args [ 3]), q->args [ 4])); break; 
case 94:result =((BT(*)(processinfo, BT, double, double, double, double))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), asreal(q->args [ 2]), asreal(q->args [ 3]), asreal(q->args [ 4])); break; 
case 95:result = asint(((double(*)(processinfo, BT, double, double, double, double))(q->func))(q, q->args [ 0], asreal(q->args [ 1]), asreal(q->args [ 2]), asreal(q->args [ 3]), asreal(q->args [ 4]))); break; 
case 96:result =((BT(*)(processinfo, double, BT, BT, BT, BT))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], q->args [ 2], q->args [ 3], q->args [ 4]); break; 
case 97:result = asint(((double(*)(processinfo, double, BT, BT, BT, BT))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], q->args [ 2], q->args [ 3], q->args [ 4])); break; 
case 98:result =((BT(*)(processinfo, double, BT, BT, BT, double))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], q->args [ 2], q->args [ 3], asreal(q->args [ 4])); break; 
case 99:result = asint(((double(*)(processinfo, double, BT, BT, BT, double))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], q->args [ 2], q->args [ 3], asreal(q->args [ 4]))); break; 
case 100:result =((BT(*)(processinfo, double, BT, BT, double, BT))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], q->args [ 2], asreal(q->args [ 3]), q->args [ 4]); break; 
case 101:result = asint(((double(*)(processinfo, double, BT, BT, double, BT))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], q->args [ 2], asreal(q->args [ 3]), q->args [ 4])); break; 
case 102:result =((BT(*)(processinfo, double, BT, BT, double, double))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], q->args [ 2], asreal(q->args [ 3]), asreal(q->args [ 4])); break; 
case 103:result = asint(((double(*)(processinfo, double, BT, BT, double, double))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], q->args [ 2], asreal(q->args [ 3]), asreal(q->args [ 4]))); break; 
case 104:result =((BT(*)(processinfo, double, BT, double, BT, BT))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], asreal(q->args [ 2]), q->args [ 3], q->args [ 4]); break; 
case 105:result = asint(((double(*)(processinfo, double, BT, double, BT, BT))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], asreal(q->args [ 2]), q->args [ 3], q->args [ 4])); break; 
case 106:result =((BT(*)(processinfo, double, BT, double, BT, double))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], asreal(q->args [ 2]), q->args [ 3], asreal(q->args [ 4])); break; 
case 107:result = asint(((double(*)(processinfo, double, BT, double, BT, double))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], asreal(q->args [ 2]), q->args [ 3], asreal(q->args [ 4]))); break; 
case 108:result =((BT(*)(processinfo, double, BT, double, double, BT))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], asreal(q->args [ 2]), asreal(q->args [ 3]), q->args [ 4]); break; 
case 109:result = asint(((double(*)(processinfo, double, BT, double, double, BT))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], asreal(q->args [ 2]), asreal(q->args [ 3]), q->args [ 4])); break; 
case 110:result =((BT(*)(processinfo, double, BT, double, double, double))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], asreal(q->args [ 2]), asreal(q->args [ 3]), asreal(q->args [ 4])); break; 
case 111:result = asint(((double(*)(processinfo, double, BT, double, double, double))(q->func))(q, asreal(q->args [ 0]), q->args [ 1], asreal(q->args [ 2]), asreal(q->args [ 3]), asreal(q->args [ 4]))); break; 
case 112:result =((BT(*)(processinfo, double, double, BT, BT, BT))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), q->args [ 2], q->args [ 3], q->args [ 4]); break; 
case 113:result = asint(((double(*)(processinfo, double, double, BT, BT, BT))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), q->args [ 2], q->args [ 3], q->args [ 4])); break; 
case 114:result =((BT(*)(processinfo, double, double, BT, BT, double))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), q->args [ 2], q->args [ 3], asreal(q->args [ 4])); break; 
case 115:result = asint(((double(*)(processinfo, double, double, BT, BT, double))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), q->args [ 2], q->args [ 3], asreal(q->args [ 4]))); break; 
case 116:result =((BT(*)(processinfo, double, double, BT, double, BT))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), q->args [ 2], asreal(q->args [ 3]), q->args [ 4]); break; 
case 117:result = asint(((double(*)(processinfo, double, double, BT, double, BT))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), q->args [ 2], asreal(q->args [ 3]), q->args [ 4])); break; 
case 118:result =((BT(*)(processinfo, double, double, BT, double, double))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), q->args [ 2], asreal(q->args [ 3]), asreal(q->args [ 4])); break; 
case 119:result = asint(((double(*)(processinfo, double, double, BT, double, double))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), q->args [ 2], asreal(q->args [ 3]), asreal(q->args [ 4]))); break; 
case 120:result =((BT(*)(processinfo, double, double, double, BT, BT))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), asreal(q->args [ 2]), q->args [ 3], q->args [ 4]); break; 
case 121:result = asint(((double(*)(processinfo, double, double, double, BT, BT))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), asreal(q->args [ 2]), q->args [ 3], q->args [ 4])); break; 
case 122:result =((BT(*)(processinfo, double, double, double, BT, double))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), asreal(q->args [ 2]), q->args [ 3], asreal(q->args [ 4])); break; 
case 123:result = asint(((double(*)(processinfo, double, double, double, BT, double))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), asreal(q->args [ 2]), q->args [ 3], asreal(q->args [ 4]))); break; 
case 124:result =((BT(*)(processinfo, double, double, double, double, BT))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), asreal(q->args [ 2]), asreal(q->args [ 3]), q->args [ 4]); break; 
case 125:result = asint(((double(*)(processinfo, double, double, double, double, BT))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), asreal(q->args [ 2]), asreal(q->args [ 3]), q->args [ 4])); break; 
case 126:result =((BT(*)(processinfo, double, double, double, double, double))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), asreal(q->args [ 2]), asreal(q->args [ 3]), asreal(q->args [ 4])); break; 
case 127:result = asint(((double(*)(processinfo, double, double, double, double, double))(q->func))(q, asreal(q->args [ 0]), asreal(q->args [ 1]), asreal(q->args [ 2]), asreal(q->args [ 3]), asreal(q->args [ 4]))); break; 
case 128:result =((BT(*)(processinfo, BT, BT, BT, BT, BT, BT))(q->func))(q, q->args [ 0], q->args [ 1], q->args [ 2], q->args [ 3], q->args [ 4], q->args [ 5]); break; 
case 129:result = asint(((double(*)(processinfo, BT, BT, BT, BT, BT, BT))(q->func))(q, q->args [ 0], q->args [ 1], q->args [ 2], q->args [ 3], q->args [ 4], q->args [ 5])); break;
     default: assertexit(0,"number of parameters not implement for threads");   
     }
    assertexit(pthread_mutex_lock (&sharedspace_mutex)==0,"lock fail2");
     q->seqelement= (q->argtype % 2) ? result : ((BT (*) (processinfo,BT))(q->deepcopyresult) ) ( q->spawningprocess,result);
      assertexit(pthread_mutex_unlock (&sharedspace_mutex)==0,"unlock fail2");
      q->aborted = 0; // must be done after seqelement is set 
    }
      if (q->freespace )  myfree(&q->space); 
   // if (q->profileindex > 0 )  (q->finishprof)(q->profileindex ,0);
}

BT processisaborted(processinfo PD,BT pin){
     processinfo q = ( processinfo)  pin;
     if (q->aborted == -1)   pthread_join(q->pid,NULL);  
    return (BT)( q->aborted);
}