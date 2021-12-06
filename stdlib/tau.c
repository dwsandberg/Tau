/* Runtime.c
 * Tests libRatings.A.dylib 1.0 as a runtime-loaded library.
 ***********************************************************/
 
#include "tau.h"
#include <stdlib.h>
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
#include <errno.h>


#define  BT long long int
#define IDXUC(a,b)  (*(BT *)((a)+8*(b)))
#define STRLEN(a)  IDXUC(a,1)
#define myalloc allocatespace

#define tocstr(filename) ( filename+16  )



typedef  struct pinfo *processinfo;


               
void assertexit(int b,char *message);

//BT loadlibrary(struct pinfo *PD,char *lib_name_root);



//Start of space allocation

#define blocksize 0xFFFFF
#define noblocks 12000
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




// start  encoding support



struct einfo {BT encodingstate;   processinfo allocatein;  };

struct einfo * neweinfo(processinfo PD,BT encodingnumber){
   static const BT x1[]={0,0};
   static const BT empty4[]={0,4,(BT) x1,(BT) x1,(BT) x1,(BT) x1};
    BT *emptyencodingstate=(BT *)myalloc(PD,6);
    emptyencodingstate[0]=encodingnumber;
    emptyencodingstate[1]=0;
    emptyencodingstate[2]=(BT) empty4;
    emptyencodingstate[3]=(BT) empty4;
    emptyencodingstate[4]=(BT)x1;
    emptyencodingstate[5]=(BT) 0;
   struct einfo *e=(struct einfo *)myalloc(PD,sizeof (struct einfo)/8);
   e->encodingstate=(BT)emptyencodingstate;
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
  e = neweinfo(PD,no);
  PD->encodings[no]=e;
 }
 return e;
 }

BT getinstance(processinfo PD,BT  encodingnumber){ 
   return startencoding(PD,encodingnumber)->encodingstate ;
}
 
 
 
BT addencoding(processinfo PD,BT encodingnumber,BT P2,BT (*add2)(processinfo,BT,BT),BT(*deepcopy)(processinfo,BT)){  
 struct einfo *e=startencoding(PD, encodingnumber)  ;
  assertexit(pthread_mutex_lock (&sharedspace_mutex)==0,"lock fail");
  BT encodingpair=   (e->allocatein == PD ) ? P2 : (deepcopy)(e->allocatein,P2)  ;
  BT newtable=(add2)(e->allocatein,e->encodingstate,encodingpair);
  e->encodingstate=newtable;
 assertexit(pthread_mutex_unlock (&sharedspace_mutex)==0,"unlock fail");
 // return  encoding
 return (( BT *) newtable)[5];
} 

// end of encoding support

// start of library support //

BT loaded[20]={0,0};
char libnames[20][100];

BT empty[2]={0,0};
BT* initialdictionary=empty;


BT* initialdict() { return initialdictionary; }



BT loadedlibs2(processinfo PD)  // returns list of loaded libraries
 {return (BT)loaded;}   


int looklibraryname(char* name) { int i;
  for(  i=0;i<loaded[1];i++){
    // fprintf(stderr,"match %d %s %s\n",i,name,libnames[i+2]);
    if (strcmp(libnames[i+2],name)==0) return i  ;
    }
   return -1;}


BT unloadlib(processinfo PD,char *libname){ 
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

BT unloadlib2(processinfo PD,char *libname){ 
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
      
    staticencodings[1]=neweinfo(&sharedspace,1);  // word encodings //
    staticencodings[2]=neweinfo(&sharedspace,2); // encoding map for assigning encoding to an integer number

/*   BT (* loaddict)(processinfo PD,BT)= dlsym(RTLD_DEFAULT,"loaddictionaryZmain2Zfileresult");
    if (!loaddict){
        fprintf(stderr,"[%s] Unable to get symbol: %s\n",__FILE__, dlerror());
       exit(EXIT_FAILURE);
    }
    loaddict(&sharedspace,getfile(&sharedspace,(BT)"1234567812345678maindictionary.data")); 
*/

    initialdictionary=(BT *)(  ((BT * )  (staticencodings[1]->encodingstate)) [4]); 
}


BT wdrepseq= ((BT *) libdesc)[1];

//fprintf(stderr,"initlib5 1\n" ); 

BT (* addlibrarywords)(processinfo PD,BT   ) = dlsym(RTLD_DEFAULT,  "addlibrarywordsZmain2Zliblib");
if (!addlibrarywords){ fprintf(stderr,"initlib5 1a\n" ); 
     BT (* addlibrarywords)(processinfo PD,BT   ) = dlsym(RTLD_DEFAULT,  "addlibrarywords");
fprintf(stderr,"initlib5 1b\n" ); 
if (!addlibrarywords){
    fprintf(stderr,"initlib5 1c\n" ); 
    fprintf(stderr,"[%s] Unable to get symbol: %s\n",__FILE__, dlerror());
    exit(EXIT_FAILURE);
}
     
}
//fprintf(stderr,"initlib5 2\n" ); 

addlibrarywords(&sharedspace,libdesc);
 
 //fprintf(stderr,"initlib5 3\n" ); 

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


BT lastentrypoint=0;

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
  lastentrypoint=(BT)dlsym(lib_handle,"entrypoint");
  stat(lib_name, &sbuf) ;  
   fprintf(stderr,"using lib %s  time: %ld\n",lib_name,sbuf.st_mtimespec.tv_sec );          
  return sbuf.st_mtimespec.tv_sec;
      
}

 
BT loadlib(processinfo PD,char *libname0)
{ char * libname=tocstr(libname0);
int i = looklibraryname(libname) ;
if (i >= 0)
{   fprintf(stderr,"did not load %s as it was loaded\n",libname) ; 
  return ((BT*)loaded[i+2])[3];}
return  loadlibrary(PD,libname) ;  
}



BT loadlib22(processinfo PD,char *libname)
{ 
int i = looklibraryname(libname) ;
if (i >= 0)
{   fprintf(stderr,"did not load %s as it was loaded\n",libname) ; 
  return ((BT*)loaded[i+2])[3];}
return  loadlibrary(PD,libname) ;  
}
 

// end of library support 


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

BT processisaborted(processinfo PD,BT pin){
     processinfo q = ( processinfo)  pin;
    if (!(q->joined)){ pthread_join(q->pid,NULL); q->joined=1;};
    return (BT)( q->aborted);
}


// start of file io

struct bitsseq  { BT type; BT length; BT  data[50]; };



BT createfile2(processinfo PD,BT bytelength, struct bitsseq *data, char * filename ) 
               {    int file=1;
                    char * name=tocstr(filename);
                    fprintf(stderr,"start createfile %s %d\n",name,file);
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
                         BT len= ((BT *) data->data[j]) [1] * 8;
                         BT len2=  len >  length ? length : len;
                         write( file,(char *)(data->data[j])+16,  len2 );
                             length=length-len2; j++;
                       }          
                }
                 if (file!=1) close(file);
                 return 1;
                 }




BT createlib2(processinfo PD,char * filename,char * otherlibs, BT bytelength, struct bitsseq *data ){
      char * libname=   tocstr(filename);
     char * otherlib= tocstr(otherlibs) ; 
     char buff[200];
     /* create the .bc file */
       sprintf(buff+16,"%s.bc",libname);
  
        createfile2(PD, bytelength , data,buff);
     /* compile to .bc file */ 
     sprintf(buff,"%s.bc",libname);
  sprintf(buff,"/usr/bin/cc -dynamiclib %s.bc %s -o %s.dylib  -init _init22 -undefined dynamic_lookup",libname,
  otherlib,libname);
   fprintf(stderr,"Createlib3 %s\n",buff);
  int err=system(buff);
  if (err ) { fprintf(stderr,"ERROR STATUS: %d \n",err); return 0;}
  else {loadlib(PD,filename); return 1;}
}
    
BT subgetfile(processinfo PD,  char *filename,BT seqtype){
  char *name= tocstr(filename);
       int fd;
    char *filedata;
    struct stat sbuf;
    static const BT empty[]={0,0};
    BT *data2,org;
 // fprintf(stderr,"openning %s\n",name); //
        org=myalloc(PD,4);
     IDXUC(org,0)=-1;
     IDXUC(org,1)=0;
     IDXUC(org,2)=0;
     IDXUC(org,3)=0;
    if ((fd = open(name, O_RDONLY)) == -1)return org;
    
    if (stat(name, &sbuf) == -1) return org;
    
    if ((filedata = mmap((caddr_t)0, sbuf.st_size, PROT_READ+PROT_WRITE, MAP_PRIVATE, fd, 0)) == (caddr_t)(-1)) return org;
    data2=(long long *) filedata;
    org=myalloc(PD,7);
     BT  filesize=sbuf.st_size,noelements; 
     int elementsin128bits;
      if (seqtype==0)  { noelements= (filesize+7)/8 ;   elementsin128bits= 2;  }
      else if (seqtype==-8)   {  noelements=filesize   ; elementsin128bits= 16; }
      else if (seqtype==-1) { noelements=(filesize  ) * 8  ; elementsin128bits= 128; }
   
     IDXUC(org,0)=filesize;
     IDXUC(org,1)=(BT)((BT * )org+3);
     IDXUC(org,2)= (BT )(filesize <= 16 ?empty:  data2);
      IDXUC(org,3)=seqtype==0?0:1;
       IDXUC(org,4)= filesize < 16 ?noelements:elementsin128bits ;
     IDXUC(org,5)=data2[0];
     IDXUC(org,6)=data2[1];
     
    data2[0]=seqtype==0?0:1;
      data2[1]= noelements-elementsin128bits ;
    close(fd);
  //  fprintf(stderr,"filename %s address %lld\n",name,(long long ) filedata);
    return org;
}

  
BT getfile(processinfo PD,char * filename){ return  subgetfile (PD,filename,0); }

BT getbytefile(processinfo PD,char * filename){  return  subgetfile (PD,filename,-8); }

BT getbitfile(processinfo PD,char * filename){ return  subgetfile (PD,filename,-1); }

BT getbytefile2(processinfo PD,char * filename){  return  subgetfile (PD,filename,-8); }

BT getbitfile2(processinfo PD,char * filename){ return  subgetfile (PD,filename,-1); }

BT getfile2(processinfo PD,char * filename){ return  subgetfile (PD,filename,0); }

// end of file io


BT noop(BT a,BT b) { return b;}

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



struct byteseq { BT type,length; char data[8];};

BT  tobyteseq ( processinfo PD,char *str) {
   int len=strlen(str);
   struct byteseq   *b=(struct byteseq   *)myalloc(PD,2+(len+7)/8);
     b->type=1;
     b->length=len;
      memcpy(b->data,str,len);
     return (BT) b;
}

int main(int argc, char **argv)    {   int i=0,count; 
           // initialize main process
    sharedspace.encodings = staticencodings;
    for(i=0; i<noencodings;i++) sharedspace.encodings[i]=0;
    signal(SIGSEGV,fatal_error_signal);
     signal(SIGBUS,fatal_error_signal);
    signal(SIGILL,fatal_error_signal);
    
     {  // load the library  
         loadlibrary(&sharedspace,argc > 1?argv[1]:"stdlib");  
     }
     
        processinfo PD=&sharedspace;
      int j;  
      processinfo p =(struct pinfo * ) malloc(sizeof (struct pinfo));
      initprocessinfo(p,PD);
      p->deepcopyresult = (BT)noop; 
      p->deepcopyseqword = (BT)noop;
       p->func=(BT)dlsym(RTLD_DEFAULT, "entrypoint");
      if (!p->func) {
        fprintf(stderr,"[%s] Unable to get symbol: %s\n",__FILE__, dlerror());
       exit(EXIT_FAILURE);
      }
      BT argsx=tobyteseq ( p,argc  > 2?argv[2]:"");  
       p->argtype=4;
       p->args=&argsx;
       p->freespace=0;
        threadbody(p);  
       if (p->aborted==1 )      { fprintf(stderr,"FATAL ERROR");  
         printf(  "FATAL ERROR");
          fflush(stdout); 
         return 1;
       }               
         
        fflush(stdout); 
         return 0;
     }
     
 BT getmachineinfo(processinfo PD) 
{  BT a = myalloc(PD,2);
   IDXUC(a,0)=tobyteseq(PD,/* "x86_64-apple-macosx10.15.0" */ "arm64-apple-macosx11.0.0");
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

BT callstack(processinfo PD,BT maxsize){
      BT r = myalloc(PD,maxsize+2);
      BT frames=backtrace(  (void*)(r+16) ,(int)maxsize);
       IDXUC(r,0)=0;
       IDXUC(r,1)=frames;
      //  fprintf(stderr,"CALLStACK %d\n",frames);
     return r;}



BT dlsymbol(processinfo PD,char * funcname) 
{if (strcmp(tocstr(funcname),"entrypoint")==0 ){
 fprintf(stderr,"dlentrypoint %lld \n",lastentrypoint);
 return lastentrypoint;
}
return (BT) dlsym(RTLD_DEFAULT,  tocstr(funcname) );}



BT toscreen(BT outputnibble ) {
return write( /* stdout */ 1,(char *) &outputnibble+1,  outputnibble & 7  );
}


double arcsin (processinfo PD, double arg)  { return asin(arg); }
  
double arccos (processinfo PD, double arg)   { return acos(arg); }

double sin2(processinfo PD, double arg )   { return sin(arg); }

double cos2(processinfo PD, double arg)  { return cos(arg); }

double tan2(processinfo PD, double arg)  { return tan(arg); }

double sqrt2(processinfo PD, double arg)  { return sqrt(arg); }

double sinreal(processinfo PD, double arg )   { return sin(arg); }

double cosreal(processinfo PD, double arg)  { return cos(arg); }

double tanreal(processinfo PD, double arg)  { return tan(arg); }

double sqrtreal(processinfo PD, double arg)  { return sqrt(arg); }

