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

void assert(int b,char *message);

BT encodeZbuiltinZTZTzerecord(processinfo PD,BT P1,BT P2);


#define DYNLIB

#define SEQLEN(a)  IDXUC(a,1)

#define SEQTYPE(a) IDXUC(a,0)

#define myalloc allocatespaceZbuiltinZint

void assert(int b,char *message);

struct spaceinfo { char * nextone,*lastone; BT *blocklist; };

struct pinfo { BT kind; // 1 if aborted
    BT message; // message if aborted (seq.word)
    BT result;  // result returned by process
    BT joined;  // has process be joined to parent?
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
    struct pinfo2 *d; // info needed to create process
               };

struct pinfo2 { BT  deepcopyresult;
               BT  deepcopyseqword;
               BT func;
               BT noargs;
               BT args[0];
               };



//Start of space allocation

#define blocksize 0xFFFFF
#define noblocks 8000
#define noencodings 40


pthread_mutex_t sharedspace_mutex=PTHREAD_MUTEX_INITIALIZER;  //for shared space
struct pinfo sharedspace={0,0,0,0,0,0};
int encnum=noencodings-1;  //protected by sharedspace_mutex



 static pthread_mutex_t memmutex=PTHREAD_MUTEX_INITIALIZER;
 static int alloccount=0;

// myalloc does not zero memory so care is needed to initialize every fld when calling.

 BT spacecount=0;


BT allocatespaceZbuiltinZint(processinfo PD, BT i)   { struct  spaceinfo *sp =&PD->space;
   sp->nextone=sp->nextone+i*8;
    spacecount+=i;
    if ((sp->nextone)>(sp->lastone) ){int k,x;   BT *b;
        assert (i*8<blocksize,"too big an object");
       //  fprintf(stderr,"mem lock\n");
        assert(pthread_mutex_lock (&memmutex)==0,"lock fail");
        assert(alloccount++<noblocks,"OUT OF SPACE");
        b=malloc(blocksize);
        // fprintf(stderr," allocate %llx\n",(BT)b);
        b[0] =(BT) sp->blocklist;
        sp->blocklist=b;
        sp->nextone=  (char *) (b+1);
        sp->lastone=sp->nextone+(blocksize)-8;
        sp->nextone=sp->nextone+i*8;
        assert(pthread_mutex_unlock (&memmutex)==0,"unlock fail");
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








BT loaded[20]={0,0};
char libnames[20][100];



int looklibraryname(char* name) { int i;
  for(  i=0;i<loaded[1];i++){
    // fprintf(stderr,"match %d %s %s\n",i,name,libnames[i+2]);
    if (strcmp(libnames[i+2],name)==0) return i  ;
    }
   return -1;}

void closelibs ( int libidx) { int i;
  for(  i=loaded[1]-1; i>=libidx;i--){ char lib_name[100];
   sprintf(lib_name,"%s.dylib",libnames[i+2]);
    void *lib_handle =dlopen(lib_name,RTLD_NOW);dlclose(lib_handle);
     fprintf(stderr,"close %s %d\n",libnames[i+2], dlclose(lib_handle) );
  }
  loaded[1]=libidx;
}

BT unloadlibZbuiltinZUTF8(processinfo PD,BT p_libname){char *libname=(char *)&IDXUC(p_libname,2);
int libidx = looklibraryname(libname);
// fprintf(stderr,"unload library %s %d\n",libname,libidx);
if (libidx > 0 ) {
  closelibs(libidx);
   } 
return 0; 
}

#ifdef DYNLIB

BT (* append) (processinfo,BT,BT);


#else

BT append(processinfo PD,BT P1, BT P2);
#endif

BT (*toUTF8)(struct pinfo *,BT );

BT *byteseqencetype;


BT initlib4(char * libname,BT * words,BT * wordlist, BT * consts,BT * libdesc) {
  // fprintf(stderr,"starting initlib4\n");
if (strcmp(libname,"stdlib")==0){
  /* only needed when initializing stdlib */
    append = dlsym(RTLD_DEFAULT, "Q2BZintzseqZTzseqZT");
    if (!append){
           fprintf(stderr,"[%s] Unable to get symbol: %s\n",__FILE__, dlerror());
          exit(EXIT_FAILURE);
    }
    toUTF8 = dlsym(RTLD_DEFAULT, "toUTF8ZUTF8Zwordzseq");
    if (!toUTF8){
        fprintf(stderr,"[%s] Unable to get symbol: %s\n",__FILE__, dlerror());
       exit(EXIT_FAILURE);
    }
    byteseqencetype= dlsym(RTLD_DEFAULT,"Q5FZbytezbitpackedseqZTzbitpackedseqZint");
    if (!byteseqencetype){
        fprintf(stderr,"[%s] Unable to get symbol: %s\n",__FILE__, dlerror());
       exit(EXIT_FAILURE);
    }
}

   BT (* relocate)(processinfo PD,BT *,BT *) = dlsym(RTLD_DEFAULT, "relocateZreconstructZwordzseqZintzseq");
   if (!relocate) {
        fprintf(stderr,"[%s] Unable to get symbol: %s\n",__FILE__, dlerror());
       exit(EXIT_FAILURE);
    }    
   BT (* encodeword)(struct pinfo *,BT *) = dlsym(RTLD_DEFAULT, "encodewordZstdlibZintzseq");
   if (!encodeword) {
        fprintf(stderr,"[%s] Unable to get symbol: %s\n",__FILE__, dlerror());
       exit(EXIT_FAILURE);
    }    

 int nowords=wordlist[3];
 int j = 4;
 int i,k;
  words[0]=0;
  words[1]=nowords;
 //  fprintf(stderr,"nowords %d\n",nowords);
 for ( k=0;k<nowords;k++) {
  int wordlength=wordlist[j+1];
  // fprintf(stderr,"%d:",k+1);
  //for(i=0;i<wordlength;i++) {  fprintf(stderr,"%c",(char)wordlist[i+j+2]);}
   words[k+2]=encodeword(&sharedspace,(wordlist+j) );
  j=j+2+wordlength;
  // fprintf(stderr,"\n");
  }
  // fprintf(stderr,"relocating const\n");
  BT * elementlist = (BT *) relocate(&sharedspace, words,consts);
  
  if ( libname[0] =='Q')
    { 
      BT (* erecordproc)(struct pinfo *)  = dlsym(RTLD_DEFAULT,libname+1);
   if (erecordproc) { 
       fprintf(stderr,"loading encoding\n");
      int i,len = elementlist[1];
      BT erec = erecordproc(&sharedspace);
       fprintf(stderr,"start build list %d\n",len);
      for(i=2; i < len+2; i++){
         BT ele = elementlist[i];
        // fprintf(stderr," %d %lld %lld\n",i,ele,erec);
         encodeZbuiltinZTZTzerecord(&sharedspace,ele,erec);
      }
       fprintf(stderr,"finish build list\n");
    } else
         fprintf(stderr,"[%s] Unable to get symbol for erec: library is not encoding %s\n",__FILE__, dlerror());
 
    }
  // for(i=0;i < consts[1]+2; i++) {   fprintf(stderr,"%lld: %lld %llx \n",  (BT)( consts+i) ,consts[i],consts[i]);}
  //  fprintf(stderr,"HI2\n");
  
 //for ( k=0;k<nowords;k++)  fprintf(stderr,"KK %d %lld\n",k,words[2+k]);
 //  fprintf(stderr,"HHH %s %d %d %lld\n",libname,nowords,j,wordlist[1]+2);
    { int i =loaded[1]++;
      char name[100];
     struct stat sbuf;
    sprintf(name,"%s.dylib",libname);
     stat(name, &sbuf);
    //   fprintf(stderr,"relocating libdesc\n");
    loaded[i+2]= relocate(&sharedspace, words,libdesc);
    ((BT*)loaded[i+2])[3]=sbuf.st_mtimespec.tv_sec;
    strcpy(libnames[i+2],libname);
    }
//   fprintf(stderr,"finish initlib4  \n");
 return 0;
  
}

BT initlib5(char * libname,BT * words,BT * wordlist, BT * consts,BT  libdesc, BT *elementlist) {
  // fprintf(stderr,"starting initlib4\n");
if (strcmp(libname,"stdlib")==0){
  /* only needed when initializing stdlib */
    append = dlsym(RTLD_DEFAULT, "Q2BZintzseqZTzseqZT");
    if (!append){
           fprintf(stderr,"[%s] Unable to get symbol: %s\n",__FILE__, dlerror());
          exit(EXIT_FAILURE);
    }
    toUTF8 = dlsym(RTLD_DEFAULT, "toUTF8ZUTF8Zwordzseq");
    if (!toUTF8){
        fprintf(stderr,"[%s] Unable to get symbol: %s\n",__FILE__, dlerror());
       exit(EXIT_FAILURE);
    }
    byteseqencetype= dlsym(RTLD_DEFAULT,"Q5FZbytezbitpackedseqZTzbitpackedseqZint");
    if (!byteseqencetype){
        fprintf(stderr,"[%s] Unable to get symbol: %s\n",__FILE__, dlerror());
       exit(EXIT_FAILURE);
    }
}

   BT (* relocate)(processinfo PD,BT *,BT *) = dlsym(RTLD_DEFAULT, "relocateZreconstructZwordzseqZintzseq");
   if (!relocate) {
        fprintf(stderr,"[%s] Unable to get symbol: %s\n",__FILE__, dlerror());
       exit(EXIT_FAILURE);
    }    
   BT (* encodeword)(struct pinfo *,BT *) = dlsym(RTLD_DEFAULT, "encodewordZstdlibZintzseq");
   if (!encodeword) {
        fprintf(stderr,"[%s] Unable to get symbol: %s\n",__FILE__, dlerror());
       exit(EXIT_FAILURE);
    }    

 int nowords=wordlist[3];
 int j = 4;
 int i,k;
  words[0]=0;
  words[1]=nowords;
 //  fprintf(stderr,"nowords %d\n",nowords);
 for ( k=0;k<nowords;k++) {
  int wordlength=wordlist[j+1];
  // fprintf(stderr,"%d:",k+1);
  //for(i=0;i<wordlength;i++) {  fprintf(stderr,"%c",(char)wordlist[i+j+2]);}
   words[k+2]=encodeword(&sharedspace,(wordlist+j) );
  j=j+2+wordlength;
  // fprintf(stderr,"\n");
  }
  // fprintf(stderr,"relocating const\n");
  relocate(&sharedspace, words,consts);
  
  if ( libname[0] =='Q')
    { 
      BT (* erecordproc)(struct pinfo *)  = dlsym(RTLD_DEFAULT,libname+1);
   if (erecordproc) { 
       fprintf(stderr,"loading encoding\n");
      int i,len = elementlist[1];
      BT erec = erecordproc(&sharedspace);
       fprintf(stderr,"start build list %d\n",len);
      for(i=2; i < len+2; i++){
         BT ele = elementlist[i];
        // fprintf(stderr," %d %lld %lld\n",i,ele,erec);
         encodeZbuiltinZTZTzerecord(&sharedspace,ele,erec);
      }
       fprintf(stderr,"finish build list\n");
    } else
         fprintf(stderr,"[%s] Unable to get symbol for erec: library is not encoding %s\n",__FILE__, dlerror());
 
    }
  // for(i=0;i < consts[1]+2; i++) {   fprintf(stderr,"%lld: %lld %llx \n",  (BT)( consts+i) ,consts[i],consts[i]);}
  //  fprintf(stderr,"HI2\n");
  
 //for ( k=0;k<nowords;k++)  fprintf(stderr,"KK %d %lld\n",k,words[2+k]);
 //  fprintf(stderr,"HHH %s %d %d %lld\n",libname,nowords,j,wordlist[1]+2);
    { int i =loaded[1]++;
      char name[100];
     struct stat sbuf;
    sprintf(name,"%s.dylib",libname);
     stat(name, &sbuf);
    //   fprintf(stderr,"relocating libdesc\n");
    loaded[i+2]= libdesc; //relocate(&sharedspace, words,libdesc);
    ((BT*)loaded[i+2])[3]=sbuf.st_mtimespec.tv_sec;
    strcpy(libnames[i+2],libname);
    }
//   fprintf(stderr,"finish initlib4  \n");
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



uint32_t jenkins_one_at_a_time_hash(char *key, size_t len)
{
    uint32_t hash, i;
    for(hash = i = 0; i < len; ++i)
    {
        hash += key[i];
        hash += (hash << 10);
        hash ^= (hash >> 6);
    }
    hash += (hash << 3);
    hash ^= (hash >> 11);
    hash += (hash << 15);
    return hash;
}

BT HASH(BT a) {  return jenkins_one_at_a_time_hash( (char *) &a , 8);}




extern BT  CLOCKPLUS (processinfo PD )
 {    BT   org=myalloc(PD,2);
     IDXUC(org,0)=clock();
     IDXUC(org,1)=0;
     return org;
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



void assert(int b,char *message){
    if (b ) return;
     fprintf(stderr,"\n%s\n",message);
    dumpstack();}





static BT LIBFUNC(processinfo PD,BT F,BT P) {
 switch (SEQLEN(P)) {
   case 0:
    return ((BT (*)(processinfo)) F) ( PD );
   case 1 :
   return ((BT (*)(processinfo,BT)) F) ( PD,IDXUC(P,2) );
  case 2 :
  return ((BT (*)(processinfo,BT,BT)) F) ( PD,IDXUC(P,2),IDXUC(P,3) );
    case 3 :
  return ((BT (*)(processinfo,BT,BT,BT)) F) ( PD,IDXUC(P,2),IDXUC(P,3),IDXUC(P,4) );

    case 4 :
  return ((BT (*)(processinfo,BT,BT,BT,BT)) F) ( PD,IDXUC(P,2),IDXUC(P,3),IDXUC(P,4) ,IDXUC(P,5));

  default:
  assert(0,"not implemented");
  }
return 55;}

BT   symboltoaddressZbuiltinZUTF8(processinfo PD,BT symname){
   char *sym_name=(char *)&IDXUC(symname,2);
   // fprintf(stderr,"datalib %s\n",sym_name);
  
   BT F = (BT) dlsym(RTLD_DEFAULT, sym_name);
   if (F)     return F;
   else {
       fprintf(stderr,"[%s] Unable to get symbol in symboltoaddress  primitive: %s\n",__FILE__, dlerror());
      exit(EXIT_FAILURE); return 1;
    }
}  

BT assertZbuiltinZwordzseq(processinfo PD,BT message)
{   PD->error =message;
    //dumpstack();
    longjmp(PD->env,1);
     return 1; }
     


               
BT executecodeZbuiltinZUTF8Zintzseq(processinfo PD,BT funcname,BT P) {
char *name=(char *)&IDXUC(funcname,2);
  BT F = (BT) dlsym(RTLD_DEFAULT, name);
    if (F) { 
      return LIBFUNC(PD,F,P);
    }
    else { 
     char *p=dlerror();
     char *p2 = "Unable to get symbol to execute ";
     int l=strlen(p);
     int l2=strlen(p2);
      BT *m =(BT*) myalloc( PD,(2+l+l2 ) ) ;
      m[0]=0; m[1]=l+l2;
      BT *q = m+2;
      while (*p2!=0) { *(q++)=*(p2++);}
      while (*p!=0) { *(q++)=*(p++);}
      
      fprintf(stderr,"[%s] Unable to get symbol to execute: %s\n",__FILE__, dlerror());
     
       BT (*towords)(processinfo PD,BT)= dlsym(RTLD_DEFAULT,"towordsZfileresultZintzseq"); 
       if (!towords) {
          fprintf(stderr,"[%s] Unable to get symbol to execute: %s\n",__FILE__, dlerror());
          exit(EXIT_FAILURE); return 1;
         }
      assertZbuiltinZwordzseq(PD,towords(PD,(BT) m));
      return 1;
    }
}


BT abortedZbuiltinZTzprocess(processinfo PD,BT pin){
     processinfo q = ( processinfo)  pin;
    if (!(q->joined)){ pthread_join(q->pid,NULL); q->joined=1;};
    return (BT)( q->kind);
}


     



BT libsZbuiltin()  // returns list of loaded libraries
 {return (BT)loaded;}   




BT  profileinfoZbuiltin(processinfo PD) { int i; char buff[100];
  static BT infoarray[30]={0};
  infoarray[1]=0;
  for(i=2;  i<= loaded[1]+1; i++)
   {  sprintf(buff,"%s$profileresult",libnames[i]);
      BT (*pinfo)(processinfo PD) = dlsym(RTLD_DEFAULT, buff);
      // fprintf(stderr,"testing %s %lld\n",buff,(BT)pinfo);
      if (pinfo) { int k;
        BT z = pinfo(PD);
         for(k=0; k<4;k++)
        //  fprintf(stderr,"XX %lld %lld \n",  ((BT *)  (((BT *) z) [k]))[0],((BT *)  (((BT *) z) [k]))[1]);
        infoarray[2+infoarray[1]++]=z;
      }
    }
    return (BT) infoarray;
    }

BT loadlibZbuiltinZUTF8(processinfo PD,BT p_libname){char *name=(char *)&IDXUC(p_libname,2);
int i = looklibraryname(name) ;
if (i >= 0)
{  // fprintf(stderr,"did not load %s as it was loaded\n",name) ; 
  return ((BT*)loaded[i+2])[3];}
return  loadlibrary(PD,name) ;  
}



BT createlibZbuiltinZbitszseqZbitszseqZoutputformat(processinfo PD,BT libname,BT otherlib,struct outputformat *t){
  char *name=(char *)&IDXUC(libname,2),buff[200];
     char *libs=(char *)&IDXUC(otherlib,2) ;
    /* create the .bc file */
     int f;
    sprintf(buff,"%s.bc",name);
     fprintf(stderr,"create %s\n",buff);
      f=open(buff,O_WRONLY+O_CREAT+O_TRUNC,S_IRWXU);
    createfilefromoutput( t,f);
     close(f);
     
   /* compile to .bc file */ 
  sprintf(buff,"/usr/bin/cc -dynamiclib %s.bc %s -o %s.dylib  -init _init22 -undefined dynamic_lookup",name,libs,name);
   fprintf(stderr,"Createlib3 %s\n",buff);
  int err=system(buff);
  if (err ) { fprintf(stderr,"ERROR STATUS: %d \n",err); return 0;}
  else {loadlibZbuiltinZUTF8(PD,libname); return 1;}
}


BT createlib3ZbuiltinZUTF8ZUTF8(processinfo PD,BT libname,BT otherlib){
  char *name=(char *)&IDXUC(libname,2),buff[200];
     char *libs=(char *)&IDXUC(otherlib,2) ;
 
  sprintf(buff,"/usr/bin/cc -dynamiclib %s.bc %s -o %s.dylib  -init _init22 -undefined dynamic_lookup",name,libs,name);
   fprintf(stderr,"Createlib3 %s\n",buff);
  int err=system(buff);
  if (err ) { fprintf(stderr,"ERROR STATUS: %d \n",err); return 0;}
  else {loadlibZbuiltinZUTF8(PD,libname); return 1;}
}



// start of file io

#include <errno.h>




BT getfileZbuiltinZUTF8(processinfo PD,BT filename){
    int fd;
    char *name=(char *)&IDXUC(filename,2);
    char *filedata;
    struct stat sbuf;
    BT *data2,org;
// fprintf(stderr,"openning %s\n",name);
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
    return org;
}

BT createfileZbuiltinZbitszseqZoutputformat(processinfo PD,BT filename,struct outputformat * t){ 
int f;
char *name=(char *)&IDXUC(filename,2);
  fprintf(stderr,"createfile %s\n",name);
 f=open(name,O_WRONLY+O_CREAT+O_TRUNC,S_IRWXU);
  createfilefromoutput( t,f);
  close(f);
return 0;
}


BT createfileZbuiltinZintzseqZintzseq(processinfo PD,BT filename,BT t){ 
//format of filename is  {struct  BT type=1; BT length;  char name[length]; char term=0; } 
//format of t is either {struct  BT type=1; BT length;  char t[length];  }
//{struct  BT type=0; BT length;  BT t[length];  }
//{struct  BT type=other; BT length, BT blocksz;   BB *data[length/blocksz] }
// where BB is on of the previous formats
int f;
char *name=(char *)&IDXUC(filename,2);
  fprintf(stderr,"createfile %s\n",name);
 f=open(name,O_WRONLY+O_CREAT+O_TRUNC,S_IRWXU);
  //printf("%lld type: %lld\n",SEQLEN(t),IDXUC(t,0));
  if (IDXUC(t,0)==0) write(f, &IDXUC(t,2),8*SEQLEN(t) );
  else  if (IDXUC(t,0)==1) write(f, &IDXUC(t,2), SEQLEN(t) );
  else
   { BT l=IDXUC(t,1);
    BT  blocksz=IDXUC(t,2);
    BT  b=IDXUC(t,3);
    int  i=1;
        assert (SEQTYPE(b)==0,"FORMAT PROBLEM");
     while (l >0) {
       int sz=SEQTYPE(IDXUC(b,i+1))==0?8:1;
       //printf(" %lld %d %lld %lld\n",l,i,SEQLEN(b),SEQLEN(IDXUC(b,i+1)));
       write(f, &IDXUC(IDXUC(b,i+1),2),sz*(l>blocksz?blocksz:l ));
       l=l-blocksz; i=i+1;
     }
     }
  close(f);
return 0;
}

BT createfileZbuiltinZUTF8Zintzseq(processinfo PD,BT filename,BT t){ return createfileZbuiltinZintzseqZintzseq(PD,filename,t);}

// end of file io

BT callstackZbuiltinZint(processinfo PD,BT maxsize){
      BT r = myalloc(PD,maxsize+2);
      BT frames=backtrace(  (void*)(r+16) ,(int)maxsize);
       IDXUC(r,0)=0;
       IDXUC(r,1)=frames;
      //  fprintf(stderr,"CALLStACK %d\n",frames);
     return r;}


// thread creation

//parent process must not terminate before child or space for parameters(encodings) may be dealocated

 

void processfunction(struct pinfo *q){
if (setjmp(q->env)!=0) {
       q->message= ((BT (*) (processinfo,BT))(q->d->deepcopyseqword) ) (q->spawningprocess,q->error);
        q->kind = 1;}
    else {BT result;
     // fprintf(stderr,"start processfunction\n");
     q->kind = 0;
     switch( q->d->noargs){
         case 0:
        result= ((BT (*) (processinfo))(q->d->func) )(q); break;
  
      case 1:
        result= ((BT (*) (processinfo,BT))(q->d->func) )(q,q->d->args[0]); break;
     case 2:
        result= ((BT (*) (processinfo,BT,BT))(q->d->func) )(q,q->d->args[0],q->d->args[1]); break;
     case 3:
        result= ((BT (*) (processinfo,BT,BT,BT))(q->d->func) )(q,q->d->args[0],q->d->args[1],q->d->args[2]); break;
     case 4:
        result= ((BT (*) (processinfo,BT,BT,BT,BT))(q->d->func) )(q,q->d->args[0],q->d->args[1],q->d->args[2],q->d->args[3]); break;
     default: assert(0,"only 1 ,2,3 or 4 arguments to process are handled");
        
     }
     // fprintf(stderr,"start result copy \n");
     assert(pthread_mutex_lock (&sharedspace_mutex)==0,"lock fail");
     q->result= ((BT (*) (processinfo,BT))(q->d->deepcopyresult) ) ( q->spawningprocess,result);
     assert(pthread_mutex_unlock (&sharedspace_mutex)==0,"unlock fail");
     // fprintf(stderr,"finish result copy\n");

    }
    if (q->freespace )  myfree(&q->space); 
    if (q->profileindex > 0 )  (q->finishprof)(q->profileindex ,0);
}

void initprocessinfo(processinfo p,processinfo PD,struct pinfo2 * pin){
       p->spawningprocess =PD;
    p->encodings = PD->encodings;
    p->kind = 0;
    p->d = pin;  
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

BT PROCESS3(processinfo PD,BT pin,BT profileidx, BT (*finishprof)(BT idx,BT x)){
 pthread_attr_t 	stackSizeAttribute;
    size_t			stackSize = 0;
  pthread_attr_init (&stackSizeAttribute);
  pthread_attr_setstacksize (&stackSizeAttribute, 1024 * 1024 * 4 );
    pthread_attr_getstacksize(&stackSizeAttribute, &stackSize); 
  /*  fprintf(stderr,"Stack size %d\n", stackSize);*/
  processinfo p=(processinfo)  myalloc(PD,sizeof (struct pinfo)/8);
  initprocessinfo(p,PD,(struct pinfo2 *) pin);
  p->profileindex = profileidx; 
  p->finishprof=finishprof;
  assert(0==pthread_create(&p->pid, &stackSizeAttribute, (void *(*)(void *) )processfunction,(void *) p),"ERROR");
  return (BT)p;
}

BT PROCESS2(processinfo PD,BT pin){
   return PROCESS3(PD,pin,0,NULL); 
}

BT noop(BT a,BT b) { 
  // fprintf(stderr, "noop %lld %lld\n",((BT *)a)[0],((BT *)a)[1]);
return b;}


BT  fill(BT *a1,struct str2 *arg1) {
arg1->type=(BT)byteseqencetype;
          //   fprintf(stderr,"KL%lld %lld %lld %s\n",arg1->type,arg1->length,(arg1->length+7 )/ 8-1,arg1->data);
      a1[0]=(BT)byteseqencetype;
      a1[1]=arg1->length;
      a1[2]=(BT)arg1;
      a1[3]=((BT *) (arg1-> data))[(arg1->length+7 )/ 8-1];
      arg1->length=(arg1->length) / 8 ;
      arg1->type=0;
      return (BT)a1;
    }


struct outputformat *output(processinfo p) {return(struct outputformat *) (p->result);}


void createfilefromoutput(struct outputformat *t,int file)
              {       if (t->data->type == 0) {
                    write(file, (char *)  t->data->data, t->bytelength);
                   }
                else {  
                    int j; int length=t->bytelength;
                           struct blockseq * blkseq=( struct blockseq *   )t->data ;
                            struct bitsseq * blks=   blkseq->seqseq;
                           int blockcount=blks->length; 
                           int count = blkseq->blksize * 8;
                        for(j=0; j < blockcount; j++)  { 
                          write( file,(char *)(blks->data[j])+16,  length < count ? length:count );
                          length=length-count;
                      }
                    
                }}
                

                            



 processinfo  step (char * func,struct str2 *arg1, struct str2 *arg2,struct str2 *arg3 ) {
 // Does not appear to allocate space correctly form pinfo as no space is given for the 3 parameters 
 processinfo PD=&sharedspace;
    int j; BT a1[4],a2[4],a3[4];
    struct pinfo2 * pin =  (struct pinfo2 * )myalloc(PD,sizeof (struct pinfo2)/8+8+8 );
      pin->deepcopyresult=(BT)noop;  
      pin->deepcopyseqword= (BT)noop;
      pin->func=(BT)dlsym(RTLD_DEFAULT, func);
      if (!pin->func) {
        fprintf(stderr,"[%s] Unable to get symbol: %s\n",__FILE__, dlerror());
       exit(EXIT_FAILURE);
    }
      
      pin->noargs=3;
      pin->args[0]=fill(a1,arg1);
      pin->args[1]= fill(a2,arg2);
      pin->args[2]= fill(a3,arg3);
      /* should be using myalloc below so space is reclaimed */
      processinfo p =(struct pinfo * ) malloc(sizeof (struct pinfo));
      initprocessinfo(p,PD,pin);
      p->freespace=0;
        processfunction(p);  
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
       return  p;}
      else 
        {  
                  
  
        return  p;
        }
}   

// end of thread creation.




//  encoding support

struct einfo {BT hashtable; BT encoded;  processinfo allocatein; };

struct einfo * neweinfo(processinfo PD){
   static const BT x1[]={0,0};
   static const BT empty4[]={0,4,(BT) x1,(BT) x1,(BT) x1,(BT) x1};
   static const BT inverted[]={(BT) empty4,0};
   struct einfo *e=(struct einfo *)myalloc(PD,sizeof (struct einfo)/8);
   e->encoded=(BT) x1;
   e->hashtable=(BT)inverted;
   e->allocatein=PD ;
   return e;
}





/* cinfo describes the constant part of encoding description. This is info the compile gernerates and only one record is generated per encoding type.
no is changed from 0 at runtime to an integer number of the encoding */
struct cinfo{ BT (* copy) (processinfo,BT) ;
             BT (* look)(processinfo,BT,BT);
             BT (*add)(processinfo,BT,BT,BT);
             BT no; 
             BT nameasword; BT persitant;
             BT typeaswords;};
             
struct einfo *staticencodings[noencodings];


struct einfo  *startencoding(processinfo PD,BT P2)
{ struct cinfo *ee = (struct cinfo *) P2;
// assign encoding number 
if (ee->no==0){
    assert(pthread_mutex_lock (&sharedspace_mutex)==0,"lock fail");
    ee->no =encnum--; 
    assert(encnum>0,"out of encoding numbers");
    assert(pthread_mutex_unlock (&sharedspace_mutex)==0,"unlock fail");
    }
 
 if (ee->persitant ) {
   struct einfo *e= staticencodings[ee->no];
   if (e==0) {
     assert(pthread_mutex_lock (&sharedspace_mutex)==0,"lock fail");
     e = neweinfo(&sharedspace );
     staticencodings[ee->no]=e;
     assert(pthread_mutex_unlock (&sharedspace_mutex)==0,"unlock fail");
        struct einfo *wordendcoding= (sharedspace.encodings[1]);
    BT data= IDX(NULL,wordendcoding->encoded,ee->nameasword);
    int i,len=SEQLEN(data) ;
    char libname[100],*p=libname;
    *p++='Q';
    for (i=1; i <=len; i++) *(p++)=(char) (IDX(NULL,data,i));
    *p++=0;
     //printf(" global %s ",libname);
     loadlibrary(&sharedspace,libname);
    }
    return e;
 }
 struct einfo *e= PD->encodings[ee->no];
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
  PD->encodings[ee->no]=e;
 }
 return e;
 }

 BT decodeZbuiltinZTzencodingZTzerecord (processinfo PD,BT P1,BT P2) { 
  BT map=startencoding(PD,P2)->encoded;
  assert ( P1>0&& P1<=SEQLEN(map), "out of range decode");
  return IDX(NULL,map,P1);
}

BT mappingZbuiltinZTzerecord(processinfo PD,BT P2){
 return startencoding(PD,P2)->encoded;
}



BT findencodeZbuiltinZTZTzerecord(processinfo PD,BT P1,BT P2){ 
  BT r;
  struct cinfo *ee = (struct cinfo *) P2;
  struct einfo *e=startencoding(PD,P2)  ;
  r= (ee->look) (PD,P1,e->hashtable);
  if (r > 0) { 
   BT *s = (BT *) myalloc(PD,3);
   s[0]=0; s[1]=1; s[2]=IDX(NULL,e->encoded,r);
   return (BT)s;
  }
  static const BT x1[]={0,0};
  return (BT)x1;
}


BT encodeZbuiltinZTZTzerecord(processinfo PD,BT P1,BT P2){  
 BT r;
 struct einfo *e=startencoding(PD,P2)  ;
  struct cinfo *ee = (struct cinfo *) P2;
  assert(pthread_mutex_lock (&sharedspace_mutex)==0,"lock fail");
  r= (ee->look) (PD,P1,e->hashtable);
if (r<=0) {
   P1=  (ee->copy) (e->allocatein,P1);
   r=SEQLEN(e->encoded)+1;
   e->encoded=append(e->allocatein,e->encoded,P1);
   e->hashtable=(ee->add)(e->allocatein,e->hashtable,r,P1);
  }
assert(pthread_mutex_unlock (&sharedspace_mutex)==0,"unlock fail");
return r;
}
// end of encoding support


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



BT addresstosymbol2ZbuiltinZint(processinfo PD,BT address){
Dl_info d; int i;
  const char * name = "unknown";
   if   (dladdr( (void *)address,&d)) name=  d.dli_sname;
  int len=strlen(name);
   BT *r = (BT *) myalloc(PD,len+2);
   r[0]=0; r[1]=len;
   for( i=0; i < len; i++)  r[i+2]=name[i]; 
 // printf("addresstosymbole2 %s\n",name);
  return (BT)r;}

struct pinfo mainprocess={0,0};





void inittau(int additional) {
  int i;
  // initialize main process
    sharedspace.encodings = staticencodings;
    for(i=0; i<noencodings;i++) sharedspace.encodings[i]=0;

    signal(SIGSEGV,fatal_error_signal);
   // signal(SIGBUS,fatal_error_signal);
   // signal(SIGILL,fatal_error_signal);
    loadlibrary(&sharedspace,"stdlib");
 if (additional==1)  loadlibrary(&sharedspace,"basic");
 
}


struct str2  *   stepresult( BT x)
    { processinfo p = (processinfo) x; 
      return (struct str2 *)(p->kind==0?p->result:p->message);
    }
    

void    stepfree ( BT x)
    { processinfo p = (processinfo) x; 
       fprintf(stderr,"space before %d\n",alloccount);
      myfree(&p->space);
       fprintf(stderr,"freed %lld\n",(BT)p->pid);
       fprintf(stderr,"space used %d\n",alloccount);
}


  
BT randomintZbuiltinZint(processinfo PD,BT len){
int randomData = open("/dev/urandom", O_RDONLY);
  BT org = myalloc(PD,2+len );
     IDXUC(org,0)=0;
     IDXUC(org,1)=len;
    if (len!=read(randomData, &IDXUC(org,2), len ))
    {
        // error, unable to read /dev/random 
    }
     
close(randomData);
  return org;
  }


BT tanZbuiltinZreal(processinfo PD, BT a)  {return asint(tan(asreal(a)));}
BT arcsinZbuiltinZreal(processinfo PD, BT a)  {return asint(asin(asreal(a)));}
BT arccosZbuiltinZreal(processinfo PD, BT a)  {return asint(acos(asreal(a)));}



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


BT getmachineinfoZbuiltin(processinfo PD) 
{  BT a = myalloc(PD,2);
   IDXUC(a,0)=tobyteseq(PD,"x86_64-apple-macosx10.12.0");
   IDXUC(a,1)=tobyteseq(PD,"e-m:o-i64:64-f80:128-n8:16:32:64-S128");
   return a;
 }





