/* Runtime.c
 * Tests libRatings.A.dylib 1.0 as a runtime-loaded library.
 ***********************************************************/
 
#include <stdio.h>
#include <stdlib.h>
#include "tau.h"
#include "math.h"
#include <dlfcn.h>
#include <execinfo.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <strings.h>
#include <signal.h>
#include <time.h>


void assertexit(int b,char *message);


#define myalloc allocatespace


struct spaceinfo { char * nextone,*lastone; BT *blocklist; };

struct pinfo { BT kind; // 1 if aborted
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
    BT noargs;
    BT *args;
               };



//Start of space allocation

#define blocksize 0xFFFFF
#define noblocks 16000
#define noencodings 40


pthread_mutex_t sharedspace_mutex=PTHREAD_MUTEX_INITIALIZER;  //for shared space
struct pinfo sharedspace={0,0,0,0,0,0};



 static pthread_mutex_t memmutex=PTHREAD_MUTEX_INITIALIZER;
 static int alloccount=0;

// myalloc does not zero memory so care is needed to initialize every fld when calling.

 BT spacecount=0;
 

BT allocatespace(processinfo PD, BT i)   { struct  spaceinfo *sp =&PD->space;
   sp->nextone=sp->nextone+i*8;
    spacecount+=i;
    if ((sp->nextone)>(sp->lastone) ){int k,x;   BT *b;
        assertexit(i*8<blocksize,"too big an object");
       //  fprintf(stderr,"mem lock\n");
        assertexit(pthread_mutex_lock (&memmutex)==0,"lock fail");
        assertexit(alloccount++<noblocks,"OUT OF SPACE");
        b=malloc(blocksize);
        // fprintf(stderr," allocate %llx\n",(BT)b);
        b[0] =(BT) sp->blocklist;
        sp->blocklist=b;
        sp->nextone=  (char *) (b+1);
        sp->lastone=sp->nextone+(blocksize)-8;
        sp->nextone=sp->nextone+i*8;
        assertexit(pthread_mutex_unlock (&memmutex)==0,"unlock fail");
        }
    return  (BT)(sp->nextone-i*8);}
    


void myfree(struct spaceinfo *sp) {int i; i =0; 
   BT *b = sp->blocklist;
   while (b!=0) {BT *next=(BT *) b[0];
    //    fprintf(stderr," free %llx\n",(BT)b);
     free(b); b=next; alloccount--;
    }
}


// End of space allocation


BT (*toUTF8)(struct pinfo *,BT );

BT *byteseqencetype;

BT (*  decodeword)(processinfo PD,BT P1);

BT loadlibrary(struct pinfo *PD,char *lib_name_root);


BT getfile(processinfo PD,BT filename);

//  encoding support



struct einfo {BT hashtable;   processinfo allocatein; };

struct einfo * neweinfo(processinfo PD){
   static const BT x1[]={0,0};
   static const BT empty4[]={0,4,(BT) x1,(BT) x1,(BT) x1,(BT) x1};
   static const BT inverted[]={0,0,(BT) empty4,(BT) empty4,(BT) x1};
   struct einfo *e=(struct einfo *)myalloc(PD,sizeof (struct einfo)/8);
   e->hashtable=(BT)inverted;
   e->allocatein=PD ;
   return e;
}
             
struct einfo *staticencodings[noencodings];

struct einfo  *startencoding(processinfo PD,BT no)
{  // assign encoding number 
   assertexit(no > 0 && no< noencodings,"invalid encoding number");
 struct einfo *e= PD->encodings[no];
 if (e==0) {
   if  ( PD->newencodings==0 && PD != &sharedspace) 
     { int i;
       struct einfo ** cpy=  (struct einfo **) myalloc(PD,noencodings); 
       for(i=0; i<noencodings ;i++)
         cpy[i]=PD->encodings[i];
       PD->encodings = cpy;
       PD->newencodings=1;  
       }
  e = neweinfo(PD);
  PD->encodings[no]=e;
 }
 return e;
 }

BT getinstance(processinfo PD,BT  encodingnumber){ 
   return startencoding(PD,encodingnumber)->hashtable ;
}
 
BT addencoding(processinfo PD,BT encodingnumber,BT P2,BT (*add2)(processinfo,BT,BT),BT(*deepcopy)(processinfo,BT)){  
 struct einfo *e=startencoding(PD, encodingnumber)  ;
  assertexit(pthread_mutex_lock (&sharedspace_mutex)==0,"lock fail");
  BT encodingpair=   (e->allocatein == PD ) ? P2 : (deepcopy)(e->allocatein,P2)  ;
  BT newtable=(add2)(e->allocatein,e->hashtable,encodingpair);
  e->hashtable=newtable;
 assertexit(pthread_mutex_unlock (&sharedspace_mutex)==0,"unlock fail");
 // return  encoding
 return (( BT *) newtable)[5];
} 


// end of encoding support


BT loaded[20]={0,0};
char libnames[20][100];

BT empty[2]={0,0};
BT* initialdictionary=empty;


BT* initialdict() { return initialdictionary; }



int looklibraryname(char* name) { int i;
  for(  i=0;i<loaded[1];i++){
    // fprintf(stderr,"match %d %s %s\n",i,name,libnames[i+2]);
    if (strcmp(libnames[i+2],name)==0) return i  ;
    }
   return -1;}


BT unloadlib(processinfo PD,BT p_libname){char *libname=(char *)&IDXUC(p_libname,2);
int libidx = looklibraryname(libname);
// fprintf(stderr,"unload library %s %d\n",libname,libidx);
if (libidx > 0 ) {
   int i;
   for(  i=loaded[1]-1; i>=libidx;i--){ char lib_name[100];
   sprintf(lib_name,"%s.dylib",libnames[i+2]);
    void *lib_handle =dlopen(lib_name,RTLD_NOW);dlclose(lib_handle);
     fprintf(stderr,"close %s %d\n",libnames[i+2], dlclose(lib_handle) );
  }
  loaded[1]=libidx;
   } 
return 0; 
}




BT initlib5(char * libname,BT  libdesc,BT baselib) {
  // fprintf(stderr,"starting initlib4\n");
  fprintf(stderr,"initlib5 %s %lld \n",libname,baselib); 
if ( baselib==1 ){
  /* only needed when initializing base lib */
    toUTF8 = dlsym(RTLD_DEFAULT, "toUTF8ZUTF8Zwordzseq");
    if (!toUTF8){
        fprintf(stderr,"[%s] Unable to get symbol: %s\n",__FILE__, dlerror());
       exit(EXIT_FAILURE);
    }                                    
     byteseqencetype= dlsym(RTLD_DEFAULT,"Q5FZbytezbitpackedseqZbytezbitpackedseqZint");
     if (!byteseqencetype) {
        fprintf(stderr,"[%s] Unable to get symbol: %s\n",__FILE__, dlerror());
       exit(EXIT_FAILURE);}
    

    decodeword= dlsym(RTLD_DEFAULT,"decodewordZwordsZword");
    if (!decodeword){
        fprintf(stderr,"[%s] Unable to get symbol: %s\n",__FILE__, dlerror());
       exit(EXIT_FAILURE);
    }
    
    staticencodings[1]=neweinfo(&sharedspace);
    staticencodings[2]=neweinfo(&sharedspace); // encoding map for assigning encoding to an integer number

   BT (* loaddict)(processinfo PD,BT)= dlsym(RTLD_DEFAULT,"loaddictionaryZmain2Zfileresult");
    if (!loaddict){
        fprintf(stderr,"[%s] Unable to get symbol: %s\n",__FILE__, dlerror());
       exit(EXIT_FAILURE);
    }
   loaddict(&sharedspace,getfile(&sharedspace,(BT)"1234567812345678maindictionary.data")); 
   fprintf( stderr, "nowords2 %lld \n",  ((BT *) (staticencodings[1]->hashtable))[1]);          

     initialdictionary=(BT *)(  ((BT * )  (staticencodings[1]->hashtable)) [4]); 
}


BT wdrepseq= ((BT *) libdesc)[1];
fprintf( stderr, "nowords %lld \n",  ((BT *)wdrepseq)[1]); 

 BT (* addwords2)(processinfo PD,BT ,BT ) = dlsym(RTLD_DEFAULT, 
       "addwordsZwordsZcharzseqzencodingstateZcharzseqzencodingrepzseq");
      if (!addwords2) {
        BT (* addwords3)(processinfo PD,BT   ) = dlsym(RTLD_DEFAULT, 
          "addwordsZwordsZcharzseqzencodingpairzseq");
          if (!addwords3){
               fprintf(stderr,"[%s] Unable to get symbol: %s\n",__FILE__, dlerror());
              exit(EXIT_FAILURE);
              }
           staticencodings[1]->hashtable= addwords3(&sharedspace,wdrepseq);
     }  else 
 staticencodings[1]->hashtable= addwords2(&sharedspace,staticencodings[1]->hashtable,wdrepseq);  
     

fprintf( stderr, "nowords3 %lld \n",  ((BT *) (staticencodings[1]->hashtable))[1]);          
 
 
 // register library 
     { int i =loaded[1]++;
      char name[100];
     struct stat sbuf;
    sprintf(name,"%s.dylib",libname);
     stat(name, &sbuf);
    loaded[i+2]= libdesc; 
    ((BT*)loaded[i+2])[3]=sbuf.st_mtimespec.tv_sec;
    strcpy(libnames[i+2],libname);
    }

  fprintf(stderr,"finish initlib5  \n");
 return 0;
  
}


BT loadlibrary(struct pinfo *PD,char *lib_name_root){
   char lib_name[200],name[100];
   struct stat sbuf;
   BT liblib;
  //  fprintf(stderr,"check %s,%d\n",lib_name_root,strlen(lib_name_root));
   sprintf(lib_name,"%s.dylib",lib_name_root);
    fprintf(stderr,"Loading %s\n",lib_name);
   void *lib_handle = dlopen(lib_name, RTLD_NOW);
    if (lib_handle==0) {
      fprintf(stderr,"[%s] Unable to open library: %s\n",__FILE__, dlerror());
     return -1;
    }  
  stat(lib_name, &sbuf) ;  
   fprintf(stderr,"using lib %s  time: %ld\n",lib_name,sbuf.st_mtimespec.tv_sec );          
  return sbuf.st_mtimespec.tv_sec;
      
}


void dumpstack()
{   void* callstack[128];
    int i, frames;
    char** strs ;
    frames = backtrace(callstack, 128);
    strs = backtrace_symbols(callstack, frames);
    for (i = 0; i < frames; ++i) {char *t=strs[i]+59,*p=t;
        while(*p!='+') p++;
        p[-1]=0;
         fprintf(stderr,"\n%lld %s",(BT)callstack[i],t);
    }
    free(strs);
    exit(-1);
}



void assertexit(int b,char *message){
    if (b ) return;
     fprintf(stderr,"\n%s\n",message);
    dumpstack();}

BT assert(processinfo PD,BT message)
{   PD->error =message;
    longjmp(PD->env,1);
     return 1; }



BT aborted(processinfo PD,BT pin){
     processinfo q = ( processinfo)  pin;
    if (!(q->joined)){ pthread_join(q->pid,NULL); q->joined=1;};
    return (BT)( q->kind);
}

BT loadedlibs()  // returns list of loaded libraries
 {return (BT)loaded;}   
 



BT loadlib(processinfo PD,BT p_libname)
{char *name=(char *)&IDXUC(p_libname,2);
int i = looklibraryname(name) ;
if (i >= 0)
{   fprintf(stderr,"did not load %s as it was loaded\n",name) ; 
  return ((BT*)loaded[i+2])[3];}
return  loadlibrary(PD,name) ;  
}

BT loadlib2(processinfo PD,char *libname)
{ 
int i = looklibraryname(libname) ;
if (i >= 0)
{   fprintf(stderr,"did not load %s as it was loaded\n",libname) ; 
  return ((BT*)loaded[i+2])[3];}
return  loadlibrary(PD,libname) ;  
}

  BT createfile2(BT bytelength, struct bitsseq *data, char * name) 
              {    int file=1;
                      if (!( strcmp("stdout",name)==0 ))  { 
                      file= open(name,O_WRONLY+O_CREAT+O_TRUNC,S_IRWXU);
                       fprintf(stderr,"createfile %s %d\n",name,file);
                     }
                 if ( data->type == 0) {
                  //  data is stored in one sequence  
                    write(file, (char *)  data->data, bytelength);
                   }
                else {  
                   // data is stored as seq.seq.int:  Each of the subseq may be of different length // 
                    int j=0; int length=bytelength;
                      while ( length > 0 )   { 
                         BT len= ((BT *) data->data[j]) [1];
                         write( file,(char *)(data->data[j])+16,  len * 8 );
                             length=length-len * 8; j++;
                       }          
                }
                 if (file!=1) close(file);
                 return 1;
                 }

BT createlib2(processinfo PD,char * libname,char * otherlib, BT bytelength, struct bitsseq *data ){
     char buff[200];
     /* create the .bc file */
       sprintf(buff,"%s.bc",libname);
  
        createfile2( bytelength , data,buff);
     /* compile to .bc file */ 
  sprintf(buff,"/usr/bin/cc -dynamiclib %s.bc %s -o %s.dylib  -init _init22 -undefined dynamic_lookup",libname,otherlib,libname);
   fprintf(stderr,"Createlib3 %s\n",buff);
  int err=system(buff);
  if (err ) { fprintf(stderr,"ERROR STATUS: %d \n",err); return 0;}
  else {loadlib2(PD,libname); return 1;}
}




// start of file io

#include <errno.h>

BT getfile(processinfo PD,BT filename){
    int fd;
    char *name=(char *)&IDXUC(filename,2);
    char *filedata;
    struct stat sbuf;
    BT *data2,org;
  //fprintf(stderr,"openning %s\n",name);
        org=myalloc(PD,4);
     IDXUC(org,0)=-1;
     IDXUC(org,1)=0;
     IDXUC(org,2)=0;
     IDXUC(org,3)=0;
    if ((fd = open(name, O_RDONLY)) == -1)return org;
    
    if (stat(name, &sbuf) == -1) return org;
    
    if ((filedata = mmap((caddr_t)0, sbuf.st_size, PROT_READ+PROT_WRITE, MAP_PRIVATE, fd, 0)) == (caddr_t)(-1)) return org;
    data2=(long long *) filedata;
    org=myalloc(PD,4);
     IDXUC(org,0)=sbuf.st_size;
     IDXUC(org,1)=data2[0];
     IDXUC(org,2)=data2[1];
     IDXUC(org,3)=(BT) data2;
    data2[0]=0;
    data2[1]=sbuf.st_size > 16 ? (sbuf.st_size+7-16)/8 : 0;
    close(fd);
  //  fprintf(stderr,"filename %s address %lld\n",name,(long long ) filedata);
    return org;
}



// end of file io



// thread creation

//parent process must not terminate before child or space for parameters(encodings) may be dealocated

void threadbody(struct pinfo *q){
if (setjmp(q->env)!=0) {
       q->message= ((BT (*) (processinfo,BT))(q->deepcopyseqword) ) (q->spawningprocess,q->error);
        q->kind = 1;}
    else {BT result;
     // fprintf(stderr,"start threadbody\n");
     q->kind = 0;
     switch( q->noargs){
         case 0:
        result= ((BT (*) (processinfo))(q->func) )(q); break;
  
      case 1:
        result= ((BT (*) (processinfo,BT))(q->func) )(q,q->args[0]); break;
     case 2:
        result= ((BT (*) (processinfo,BT,BT))(q->func) )(q,q->args[0],q->args[1]); break;
     case 3:
        result= ((BT (*) (processinfo,BT,BT,BT))(q->func) )(q,q->args[0],q->args[1],q->args[2]); break;
     case 4:
        result= ((BT (*) (processinfo,BT,BT,BT,BT))(q->func) )(q,q->args[0],q->args[1],q->args[2],q->args[3]); break;
    case 5:
        result= ((BT (*) (processinfo,BT,BT,BT,BT,BT))(q->func) )(q,q->args[0],q->args[1],q->args[2],q->args[3],q->args[4]); break;
    case 6:
        result= ((BT (*) (processinfo,BT,BT,BT,BT,BT,BT))(q->func) )(q,q->args[0],q->args[1],q->args[2],q->args[3],q->args[4],q->args[5]); break;
     default: assertexit(0,"only 1 ,2,3, 4 or 5 arguments to process are handled");
        
     }
     // fprintf(stderr,"start result copy \n"); //
     assertexit(pthread_mutex_lock (&sharedspace_mutex)==0,"lock fail");
     q->result= ((BT (*) (processinfo,BT))(q->deepcopyresult) ) ( q->spawningprocess,result);
     assertexit(pthread_mutex_unlock (&sharedspace_mutex)==0,"unlock fail");
     // fprintf(stderr,"finish result copy\n"); //
    }
    if (q->freespace )  myfree(&q->space); 
    if (q->profileindex > 0 )  (q->finishprof)(q->profileindex ,0);
}

void initprocessinfo(processinfo p,processinfo PD){
    p->spawningprocess =PD;
    p->encodings = PD->encodings;
    p->kind = 0;
    p->pid = pthread_self ();
    p->joined =0 ;
    p->space.nextone =0;
    p->space.lastone =0;
    p->space.blocklist = 0;
    p->error =0;
    p->message =0;
    p->result =0;
    p->profileindex = 0;
    p->freespace=1;
    p->newencodings=0;
}





BT createthread(processinfo PD ,BT  deepcopyresult  ,BT  deepcopyseqword  ,BT func,BT * args ){
BT profileidx=0;
BT (*finishprof)(BT idx,BT x) =NULL;
  pthread_attr_t 	stackSizeAttribute;
  size_t			stackSize = 0;
  pthread_attr_init (&stackSizeAttribute);
  pthread_attr_setstacksize (&stackSizeAttribute, 1024 * 1024 * 12 *8 );
  pthread_attr_getstacksize(&stackSizeAttribute, &stackSize); 
  /*  fprintf(stderr,"Stack size %d\n", stackSize);*/
  processinfo p=(processinfo)  myalloc(PD,(sizeof (struct pinfo)+7)/8);
  initprocessinfo(p,PD);
  p->deepcopyresult =  deepcopyresult; 
    p->deepcopyseqword =  deepcopyseqword;
    p->func= func;
    p->noargs=args[1];
    p->args= args+2;

  p->profileindex = profileidx; 
  p->finishprof=finishprof;
  assertexit(0==pthread_create(&p->pid, &stackSizeAttribute, (void *(*)(void *) )threadbody,(void *) p),"ERROR");
  return (BT)p;
}


BT noop(BT a,BT b) { return b;}

  


// end of thread creation.


volatile sig_atomic_t fatal_error_in_progress = 0;

void
fatal_error_signal (int sig)
{
  /* Since this handler is established for more than one kind of signal, 
     it might still get invoked recursively by delivery of some other kind
     of signal.  Use a static variable to keep track of that. */
  if (fatal_error_in_progress)
    raise (sig);
  fatal_error_in_progress = 1;
   dumpstack();
  signal (sig, SIG_DFL);
  raise (sig);
}


struct byteseq { BT type,length,*seq,type2,length2; char data[8];};

BT  tobyteseq ( processinfo PD,char *str) {
   int len=strlen(str);
   struct byteseq   *b=(struct byteseq   *)myalloc(PD,5+(len+7)/8);
     b->type=(BT)byteseqencetype;
     b->length=len;
     b->seq =(BT *) &(b->type2);
     b->type2=0;
     b->length2=(len+7)/8;
     memcpy(b->data,str,len);
     return (BT) b;
}


int main(int argc, char **argv)    {   int i=0,count; 
        char argstr[500]; {int i;
           // initialize main process
    sharedspace.encodings = staticencodings;
    for(i=0; i<noencodings;i++) sharedspace.encodings[i]=0;
    signal(SIGSEGV,fatal_error_signal);
     signal(SIGBUS,fatal_error_signal);
    signal(SIGILL,fatal_error_signal);
  } 
       for(count=1;argc > count; count++){ // combine arguements
        int j=0;
            while( argv[count][j] != 0 ) { argstr[i++]=argv[count][j++];}
            argstr[i++]=' '; 
     }   
     argstr[i++]=0;
     {  // load the library  
       char libstr[100]="stdlib";
       int k=0;
       i=0; while( argstr[i]==' ') i++;
       if (argstr[i]=='L' ) { i++;
         while( argstr[i]==' ') i++;
         while( argstr[i]!=' ' & argstr[i]!=0) libstr[k++]=argstr[i++]; 
         libstr[k]=0;
       }
        loadlibrary(&sharedspace,libstr);  
     }
        processinfo PD=&sharedspace;
      int j;  
      processinfo p =(struct pinfo * ) malloc(sizeof (struct pinfo));
      initprocessinfo(p,PD);
      p->deepcopyresult = (BT)noop; 
      p->deepcopyseqword = (BT)noop;
      p->func=(BT)dlsym(RTLD_DEFAULT, "mainZmain2Zintzseq");
      if (!p->func) {
        fprintf(stderr,"[%s] Unable to get symbol: %s\n",__FILE__, dlerror());
       exit(EXIT_FAILURE);
      }
      BT argsx=tobyteseq ( p, argstr);
       p->noargs=1;
       p->args=&argsx;
       p->freespace=0;
        threadbody(p);  
       if (p->kind==1 )   { 
          char *header = "Status: 500 Error\r\nContent-Type: text/html\r\n\r\n";
        BT s=toUTF8(PD,p->message);
        BT i,seqlen=IDXUC(s,1);
        BT *r=(BT *)myalloc( PD,(2+strlen(header)+seqlen ));
        r[1]=strlen(header)+seqlen;
        r[0]=0;
        BT *t=r+2;
        while (*header !=0)   *(t++)=*(header++);
        for (i=1; i<=seqlen;i++)
         { BT tmp=IDX(PD,s,i);*(t++)=  tmp;}
         p->message=(BT)r;
         }         
         
        fflush(stdout); 
         return 0;
     }
     
 
 
 
 BT getmachineinfo(processinfo PD) 
{  BT a = myalloc(PD,2);
   IDXUC(a,0)=tobyteseq(PD,"x86_64-apple-macosx10.15.0");
   IDXUC(a,1)=tobyteseq(PD,"e-m:o-i64:64-f80:128-n8:16:32:64-S128");
   return a;
 }

BT currenttime() { 
     BT T1970=210866716800;
     time_t seconds;
     seconds = time(NULL);
     return T1970+seconds;
}
    
BT randomint (processinfo PD,BT len){
     int randomData = open("/dev/urandom", O_RDONLY);
     BT org = myalloc(PD,2+len );
     IDXUC(org,0)=0;
     IDXUC(org,1)=len;
     if (len!=read(randomData, &IDXUC(org,2), len*8 )) {      /* error, unable to read /dev/random  */ }    
     close(randomData);
     return org;
  }

BT addresstosymbol2(processinfo PD,BT address){
Dl_info d; int i;
  const char * name = "unknown";
   if   (dladdr( (void *)address,&d)) name=  d.dli_sname;
  int len=strlen(name);
   BT *r = (BT *) myalloc(PD,len+2);
   r[0]=0; r[1]=len;
   for( i=0; i < len; i++)  r[i+2]=name[i]; 
 // printf("addresstosymbole2 %s\n",name);
  return (BT)r;}
  
/* BT   symboltoaddress(processinfo PD,BT symname){
   char *sym_name=(char *)&IDXUC(symname,2);
   // fprintf(stderr,"datalib %s\n",sym_name);
  
   BT F = (BT) dlsym(RTLD_DEFAULT, sym_name);
   if (F)     return F;
   else {
       fprintf(stderr,"[%s] Unable to get symbol in symboltoaddress  primitive: %s\n",__FILE__, dlerror());
      exit(EXIT_FAILURE); return 1;
    }
} */
 
BT callstack(processinfo PD,BT maxsize){
      BT r = myalloc(PD,maxsize+2);
      BT frames=backtrace(  (void*)(r+16) ,(int)maxsize);
       IDXUC(r,0)=0;
       IDXUC(r,1)=frames;
      //  fprintf(stderr,"CALLStACK %d\n",frames);
     return r;}
     
BT dlsymbol(processinfo PD,BT funcname) 
{return (BT) dlsym(RTLD_DEFAULT, (char *)&IDXUC(funcname,2));}


BT toscreen(BT outputnibble ) {
return write( /* stdout */ 1,(char *) &outputnibble+1,  outputnibble & 7  );
}

BT callidx3(BT PD, BT * seq, BT idx)  
 {   if (seq[0]==0 )  return seq[idx+1];
 BT (* callit)(BT,BT *,BT ) = (  BT (*)(BT,BT * ,BT )  ) seq[0];
    return  (callit)(PD,seq,idx);}
