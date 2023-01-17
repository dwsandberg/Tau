 
#include "tau.h"
#include <stdlib.h>
#include "math.h"
#include <execinfo.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <string.h>
#include <signal.h>
#include <time.h>
#include <errno.h>




#define  BT long long int
#define IDXUC(a,b)  (*(BT *)((a)+8*(b)))
#define STRLEN(a)  IDXUC(a,1)
#define myalloc allocatespace

#define tocstr(filename) ( filename+16  )



typedef  struct pinfo *processinfo;

char basedir[100];

               
void assertexit(int b,char *message);


//Start of space allocation

#define blocksize 0xFFFFF
#define noblocks 12000


pthread_mutex_t sharedspace_mutex=PTHREAD_MUTEX_INITIALIZER;  //for shared space
struct pinfo sharedspace={0,0,0,0,0,0};
static pthread_mutex_t memmutex=PTHREAD_MUTEX_INITIALIZER;
static int alloccount=0;

// myalloc does not zero memory so care is needed to initialize every fld when calling.

// BT profiledata; 
// BT profilevector;

BT spacecount2=0;
  
BT spacecount() {return spacecount2;}

BT allocatespace(processinfo PD, BT i)   { struct  spaceinfo *sp =&PD->space;
   sp->nextone=sp->nextone+i*8;
    spacecount2+=i;
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

struct encodingstate { BT * all;BT length;BT *table;BT last;};
struct einfo {struct encodingstate *encodingstate;  BT eno; processinfo allocatein;   };

BT currentprocess(processinfo  PD)  {
return (BT)PD;}

struct encodingstate * addencoding4(processinfo PD, struct einfo * e ,BT  data  
,struct encodingstate * (*add2)(processinfo,struct einfo *,BT)
){
  assertexit(pthread_mutex_lock (&sharedspace_mutex)==0,"lock fail");
  processinfo  allocatein=e->allocatein ;
  struct encodingstate * newtable=(add2)(allocatein,e, data);
 assertexit(pthread_mutex_unlock (&sharedspace_mutex)==0,"unlock fail");
 return ( newtable );
}  

struct encodingstate * addencoding5(processinfo PD, struct einfo * e ,BT * data  
,struct encodingstate * (*add2)(processinfo,struct einfo *,BT)
){
  assertexit(pthread_mutex_lock (&sharedspace_mutex)==0,"lock fail");
  processinfo  allocatein=e->allocatein ;
  struct encodingstate * newtable=(add2)(allocatein,e,* data);
 assertexit(pthread_mutex_unlock (&sharedspace_mutex)==0,"unlock fail");
 return ( newtable );
} 

BT critical(processinfo PD,BT P1, BT P2,processinfo allocatein, BT   (*add2)(processinfo,BT,BT)
)
{ 
 assertexit(pthread_mutex_lock (&sharedspace_mutex)==0,"lock fail");
   BT result=(add2)(allocatein,P1 ,P2);
  assertexit(pthread_mutex_unlock (&sharedspace_mutex)==0,"unlock fail");
  return result;
}

// end of encoding support

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




// start of file io

int myopen(char * name) {
char *p;
 char tmp[200];
 for(p=name;*p!=0;p++){
   strncpy(tmp,name,sizeof(tmp));
   tmp[ p-name]=0;
  if (*p=='/') {
   int status=  mkdir(tmp,0777) ;
   int error=errno;
  // fprintf(stderr,"%s %d\n",tmp,status);
    status =( status==0|| errno==EEXIST) ? 0 : errno ;
    if (status !=0 ) return status;
   
 //   printf("%s\n",tmp);
 }}
   int fp= open(name,O_CREAT |O_RDWR |O_TRUNC,0666);
   if (fp < 0 ) return errno;
    fchmod(fp, S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP );
 return fp;
 }
 
 struct bitsseq  { BT type; BT length; BT * data[50]; };

 
BT createfile3(processinfo PD, struct bitsseq *data, char * filename )  {
int file=1,i;
char * name=tocstr(filename);
if (!( strcmp("stdout",name)==0 )) file=myopen(name);
for (i=0; i < data->length;i++){ 
   BT len= ( data->data[i])[1] ;
   //  fprintf(stderr,"seqlen %lld  \n",len);
   write(file, (char *)(data->data[i])+16, len);
}
if (file!=1) {              
	fprintf(stderr,"createfile %s %lld %lld \n",name,data->length ,lseek(file, 0, SEEK_CUR));
	close(file);
}
return 0;
}


 void prepare(char *otherlib,char *str,char *replace){
  char  *o=otherlib ,*p=str+16; 
     otherlib[0]=0;
      while (*p!=0) { *o=*p;
           if (*p==' ') { strcpy(o,replace); o=o+strlen(replace)-1;} 
           p++;o++;
      }
    }
    
#ifdef LIBRARY 

#include <dlfcn.h>

BT loadlibrary(char *lib_name_root){
   char lib_name[200];
   struct stat sbuf;
   BT liblib;
  //  fprintf(stderr,"check %s,%d\n",lib_name_root,strlen(lib_name_root));
   sprintf(lib_name,"%s/%s",basedir,lib_name_root);
 // sprintf(lib_name,"%s.dylib",lib_name_root);
   // fprintf(stderr,"Loading %s\n",lib_name);
   void *lib_handle = dlopen(lib_name, RTLD_NOW);
    if (lib_handle==0) {
      fprintf(stderr,"[%s] Unable to open library: %s\n",__FILE__, dlerror());
     return -1;
    }  
  stat(lib_name, &sbuf) ;  
   fprintf(stderr,"using lib %s  time: %ld\n",lib_name,sbuf.st_mtimespec.tv_sec );          
  return sbuf.st_mtimespec.tv_sec;  
}

#else

 void initializewords(processinfo PD);

#endif


    
BT subgetfile(processinfo PD,  char *filename,BT seqtype){
  char *name= tocstr(filename);
       int fd;
    char *filedata;
    struct stat sbuf;
    static const BT empty[]={0,0};
    BT *data2,org;
//  fprintf(stderr,"openning %s\n",name);  
        org=myalloc(PD,12);
     IDXUC(org,0)=1;
     IDXUC(org,1)=0;
     IDXUC(org,2)=0;
     IDXUC(org,3)=0;
    if ((fd = open(name, O_RDONLY)) == -1)return org;
    
    if (stat(name, &sbuf) == -1) return org;
    
    BT  filesize=sbuf.st_size,noelements; 
    if (filesize == 0) { data2=(BT *)empty;} 
    else {
     if ((filedata = mmap((caddr_t)0, sbuf.st_size, PROT_READ+PROT_WRITE, MAP_PRIVATE, fd, 0)) == (caddr_t)(-1)) return org;
     data2=(long long *) filedata;
    }
     int elementsin128bits;
     if (seqtype==0)  { noelements= (filesize+7)/8 ;   elementsin128bits= 2;  }
     else if (seqtype==-8)   {  noelements=filesize   ; elementsin128bits= 16; }
     else if (seqtype==-1) { noelements=(filesize  ) * 8  ; elementsin128bits= 128; }
   
     IDXUC(org,0)=0;
     IDXUC(org,1)=(BT)((BT * )org+5);
     IDXUC(org,2)= (BT )(filesize <= 16 ?empty:  data2);
     IDXUC(org,3)=(BT)((BT * )org+9);
     IDXUC(org,4)= (BT )(filesize <= 16 ?empty:  data2);
     
     IDXUC(org,5)=seqtype==0?0:1;
     IDXUC(org,6)= filesize < 16 ?noelements:elementsin128bits ;
     IDXUC(org,7)=data2[0];
     IDXUC(org,8)=data2[1];
     
     IDXUC(org,9)=0;
     IDXUC(org,10)=1;
     IDXUC(org,11)=(BT)((BT * )org+5);
     
     if (filesize > 0 ){
       data2[0]=seqtype==0?0:1;
       data2[1]= noelements-elementsin128bits ;
     }
     close(fd);
  //  fprintf(stderr,"filename %s address %lld\n",name,(long long ) filedata);
    return org;
}

  
//BT getfile(processinfo PD,char * filename){ return  subgetfile (PD,filename,0); }

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

struct einfo einit ={0,0};

struct einfo *staticencodings[2];

BT mainentry(BT,BT);



int main(int argc, char **argv)    {   int i=0,count; 

strcpy(basedir,argv[0]);
for(i=strlen(basedir)-1 ;i >=0 ;i--) if (basedir[i]=='/') {basedir[i]=0; break;}

           // initialize main process
    sharedspace.encodings = staticencodings;
    sharedspace.lasteinfo = &einit;
    sharedspace.encodings[0]=(struct einfo *)(0);
    sharedspace.encodings[1]=(struct einfo *)(0);
     signal(SIGSEGV,fatal_error_signal);
     signal(SIGBUS,fatal_error_signal);
    signal(SIGILL,fatal_error_signal);
 
#ifdef LIBRARY 
      int startarg=2;
     fprintf(stderr,"DYLIB VERSION\n");
    if (argc==0)  fprintf(stderr,"must have compiled library as first argument"); 
     fprintf(stderr, "Library %s  \n ",argv[1]  );    
     loadlibrary(&sharedspace, argv[1]); 
#else
  int startarg=1;
 initializewords(&sharedspace) ;

     
#endif
  
  
 //     BT   entrypoint=((BT*)loaded[loaded[1]+1])[2];

      processinfo PD=&sharedspace;
      int j;  
      processinfo p =(struct pinfo * ) malloc(sizeof (struct pinfo));
      initprocessinfo(p,PD);
      p->deepcopyresult = (BT)noop; 
      p->deepcopyseqword = (BT)noop;
       p->func=(BT)&mainentry;
   
      char allargs[2000]="";
       for(j=startarg; j < argc; j++) 
        { strcat(allargs,argv[j]); strcat(allargs," ");}
       BT argsx=tobyteseq ( p,allargs);  
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
   IDXUC(a,0)=tobyteseq(PD,/* "x86_64-apple-macosx10.15.0" */ "arm64-apple-macosx13.0.0");
   IDXUC(a,1)=tobyteseq(PD,"e-m:o-i64:64-f80:128-n8:16:32:64-S128");
   return a;
 }
 
BT currenttime() { 
     BT T1970=210866716800;
     time_t seconds;
     seconds = time(NULL);
     return T1970+seconds;
}

BT threadclock() { struct timespec ts;
if (clock_gettime(CLOCK_THREAD_CPUTIME_ID, &ts) == -1) return -1; 

return ts.tv_sec * 1000000000 + ts.tv_nsec; 
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

BT callstack(processinfo PD,BT maxsize){
      BT r = myalloc(PD,maxsize+2);
      BT frames=backtrace(  (void*)(r+16) ,(int)maxsize);
       IDXUC(r,0)=0;
       IDXUC(r,1)=frames;
      //  fprintf(stderr,"CALLStACK %d\n",frames);
     return r;}

// BT dlsymbol(processinfo PD,char * funcname) {return (BT) dlsym(RTLD_DEFAULT,  tocstr(funcname) );}

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

