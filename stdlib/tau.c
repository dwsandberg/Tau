 
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


               
void assertexit(int b,char *message);


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

 
 BT loadedLibs(processinfo PD)  // returns list of loaded libraries
 {return (BT)loaded;}   
  


int looklibraryname(char* name) { int i;
  for(  i=0;i<loaded[1];i++){
    // fprintf(stderr,"match %d %s %s\n",i,name,libnames[i+2]);
    if (strcmp(libnames[i+2],name)==0) return i  ;
    }
   return -1;}

BT initlib5(char * libname,BT  libdesc,BT baselib) {
  // fprintf(stderr,"starting initlib4\n");
  //fprintf(stderr,"initlib5 %s %lld \n",libname,baselib); 
  static BT (* addlibrarywords)(processinfo PD,BT   );
if ( baselib ){
  /* only needed when initializing base lib */
      
    staticencodings[1]=neweinfo(&sharedspace,1);  // word encodings //
    staticencodings[2]=neweinfo(&sharedspace,2); // encoding map for assigning encoding to an integer number

    addlibrarywords  = ( BT (* )(processinfo PD,BT   )) baselib; 
}

addlibrarywords(&sharedspace,libdesc);

 // register library 
     { int i =loaded[1]++;
      char name[100];
     struct stat sbuf;
    sprintf(name,"%s.dylib",libname);
     stat(name, &sbuf);
    loaded[i+2]= libdesc; 
    ((BT*)loaded[i+2])[3]=0;
    strcpy(libnames[i+2],libname);
    }

// fprintf(stderr,"finish initlib5  \n");
return 0;
  
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
int file=1;
                    char * name=tocstr(filename);
                       if (!( strcmp("stdout",name)==0 ))  { 
                      file=myopen(name);
                       fprintf(stderr,"createfile %s %lld  \n",name,data->length );
                     }
                     int i;
                 for (i=0; i < data->length;i++){ 
                  BT len= ( data->data[i])[1] ;
          //        fprintf(stderr,"seqlen %lld  \n",len);
                     write(file, (char *)(data->data[i])+16, len);
                     }
                 if (file!=1) close(file);
         //         fprintf(stderr,"finish createfile %s %d\n",name,file);
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

BT loadlibrary(struct pinfo *PD,char *lib_name_root){
   char lib_name[200],name[100];
   struct stat sbuf;
   BT liblib;
    int i = looklibraryname(lib_name_root) ;
  if (i >= 0)
   {   // fprintf(stderr,"did not load %s as it was loaded\n",libname) ; 
     return ((BT*)loaded[i+2])[3];}
  //  fprintf(stderr,"check %s,%d\n",lib_name_root,strlen(lib_name_root));
   sprintf(lib_name,"built/%s.dylib",lib_name_root);
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




void init_libs();


//  cc stdlib/*.c  tmp/stdlib.bc tmp/common.bc tmp/tools.bc


#endif


    
BT subgetfile(processinfo PD,  char *filename,BT seqtype){
  char *name= tocstr(filename);
       int fd;
    char *filedata;
    struct stat sbuf;
    static const BT empty[]={0,0};
    BT *data2,org;
//  fprintf(stderr,"openning %s\n",name);  
        org=myalloc(PD,4);
     IDXUC(org,0)=1;
     IDXUC(org,1)=0;
     IDXUC(org,2)=0;
     IDXUC(org,3)=0;
    if ((fd = open(name, O_RDONLY)) == -1)return org;
    
    if (stat(name, &sbuf) == -1) return org;
    
    if ((filedata = mmap((caddr_t)0, sbuf.st_size, PROT_READ+PROT_WRITE, MAP_PRIVATE, fd, 0)) == (caddr_t)(-1)) return org;
    data2=(long long *) filedata;
    org=myalloc(PD,12);
     BT  filesize=sbuf.st_size,noelements; 
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
     
     data2[0]=seqtype==0?0:1;
     data2[1]= noelements-elementsin128bits ;
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


int main(int argc, char **argv)    {   int i=0,count; 
#ifdef LIBRARY 
     fprintf(stderr,"DYLIB VERSION\n");
    if (argc==0)  fprintf(stderr,"must have compiled library as first argument"); 
#endif  
           // initialize main process
    sharedspace.encodings = staticencodings;
    for(i=0; i<noencodings;i++) sharedspace.encodings[i]=0;
    signal(SIGSEGV,fatal_error_signal);
     signal(SIGBUS,fatal_error_signal);
    signal(SIGILL,fatal_error_signal);
 
 #ifdef LIBRARY 
   int startarg=2;
     loadlibrary(&sharedspace, argv[1]); 
#else
  int startarg=1;
  init_libs();
#endif
  
      BT   entrypoint=((BT*)loaded[loaded[1]+1])[2];

      processinfo PD=&sharedspace;
      int j;  
      processinfo p =(struct pinfo * ) malloc(sizeof (struct pinfo));
      initprocessinfo(p,PD);
      p->deepcopyresult = (BT)noop; 
      p->deepcopyseqword = (BT)noop;
       p->func=entrypoint;
   
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

