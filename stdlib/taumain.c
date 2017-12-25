/*
 *  SCGI C Library
 *  By Sam Alexander
 *
 *  Version 0.2, Last Updated:  01 Mar 2014
 *
 *  On the web... http://www.xamuel.com/scgilib/
 *                http://www.xamuel.com/scgilib/helloworld/
 *
 *  helloworld.c - SCGI Library example file
 *                 Creates a server (on port 8000) to listen for SCGI and respond with Hello World!
 *
 *  To actually make this work, one must configure one's webserver to redirect (certain) traffic to
 *  port 8000 using the SCGI protocol.  How to do this varies from webserver to webserver.
 *  Of course, 8000 can be replaced with whatever port number you want.
 *
 *  For example, on the xamuel.com Apache server, first I installed the mod-scgi module, then I added
 *  the following line in etc/apache2/apache2.conf :
 *    SCGIMount /scgilib/helloworld/ 127.0.0.1:8000
 *  Then I restarted Apache.
 *  This tells Apache that when anyone requests /scgilib/helloworld/, Apache is to translate the request
 *  into the SCGI protocol, forward it to port 8000, obtain a response, and forward the response back to
 *  whoever made the original request.
 *
 *  Copyright/license:  MIT
 */

#include "scgilib.h"
#include <stdio.h>
#include <string.h>


#include <stdlib.h>


#define HELLOWORLDPORT 8000

/*
 * nginx does not correctly implement the SCGI protocol.
 * After much hair-pulling, I discovered that as of version
 * 1.1.19, nginx will accept SCGI responses if they send
 * the header "HTTP/1.1 200 OK" and no other headers.
 *
 * To make helloworld.c work with Apache, comment out the following line.
 * To make it work with nginx, leave the following line defined.
 *
 */

//#define SUPPORT_FOR_BUGGY_NGINX

#define  BT long long int

struct str2 { BT  type;
               BT  length;
               char data[500];
               };

typedef  struct str2 *pstr2;

struct strblock{ BT type; BT length; BT blocksz;   pstr2 *data; };

BT  step ( char * func,struct str2 *rname,struct str2 *func2,struct str2 *buff ) ; /* defined in tau.c */
struct str2  *   stepresult( BT x);  /* defined in tau.c */
void    stepfree ( BT x); /* defined in tau.c */
void inittau(int additional); /* defined in tau.c */



int scgi_sendtau( scgi_request *req, BT process)
{ 
  struct str2 *txt = stepresult(process);
  int len = txt->length;
  scgi_desc *d = req->descriptor;
 
  /*
   * If more is being sent than we've allocated space for, then allocate more space
   */
  if ( len >= d->outbufsize - 5 ){
    char *newbuf = calloc( len + 6, sizeof(char) );

    if ( !newbuf ) return 0;
    free( d->outbuf );
    d->outbuf = newbuf;
    d->outbufsize = len + 6;
  }
  /* copy the data */
  
  if  (txt->type==1) {
    memcpy(d->outbuf,txt->data,len);
  } else{
     struct strblock *d2 = (struct strblock *) txt;
     
   //  printf("XX %lld\n",d2->blocksz );
 pstr2 *data2 = (d2->data)+2;
// printf("complex send %lld %lld\n", data2[0]->length,data2[1]->length);
  int remaining = len;
  int blocksz= d2->blocksz;
  char *p=d->outbuf;
  while (remaining > 0 ) {
   // printf("remaining %d %lld\n",remaining,(*data2)->length );
     memcpy( p,(*data2)->data, remaining > blocksz ? blocksz: remaining );
     remaining-=blocksz; data2++; p+=blocksz;
    }
 }
// { int jj;
// for (jj=0;jj<len; jj++) printf("%c",d->outbuf[jj]); 
 //         printf("\n" );}
  d->outbuflen = len;

  /*
   * The actual physical transmission will be handled by the scgi_flush_response function,
   * once the socket is ready to receive it.
   */

 stepfree ( process);
  return 1;
}

int serverloop(void)
{  
  int connections;

  /*
   * Attempt to initialize the SCGI Library and make it listen on a port
   */

  if ( scgi_initialize( HELLOWORLDPORT ) )
    printf( "Successfully initialized the SCGI library.  Listening on port %d.\n", HELLOWORLDPORT );
  else
  {
    printf(	"Could not listen for incoming connections on port %d.\n"
		"Aborting helloworld.\n\n", HELLOWORLDPORT );
    return 0;
  }

  /*
   * Enter an infinite loop, serving up responses to SCGI connections forever.
   */
  while ( 1 )
  {
    /*
     * Check for connections ten times per second (once per 100000 microseconds).
     * A typical server (such as this helloworld server) will spend the vast majority of its time sleeping.
     * Nothing magical about 100000 microseconds, an SCGI Library user can call the library as often or rarely
     * as desired (of course, if you wait foreeeever, eventually your webserver will issue an "Internal Server Error").
     */
    usleep(100000);

#define MAX_CONNECTIONS_TO_ACCEPT_AT_ONCE 5

    connections = 0;

    while ( connections < MAX_CONNECTIONS_TO_ACCEPT_AT_ONCE )
    {
      /*
       * If any connections are awaiting the server's attention, scgi_recv() will output a pointer to one of them.
       * Otherwise, it will return NULL.
       */
      scgi_request *req = scgi_recv();
      int dead;

      if ( req != NULL )
      {
        /*
         * Got a connection!
         */
        connections++;

        /*
         * Since there is no way to check whether memory has been free'd, let's give the library a way to
         * let us know whether the request still exists in memory or not, by giving it the address of an
         * int.  Once we've done this, we can check the int at any time, to see whether the request still
         * exists in memory.
         */
        dead = 0;
        req->dead = &dead;

  
        struct str2  buff;
        struct str2  ruser;
        struct str2  func;

        printf( "SCGI C Library received an SCGI connection on port %d. user: %s\n", req->descriptor->port->port, req->remote_user);
        { /*set up request */
           char *p=req->body;
           char *t=buff.data;
           buff.type=1;
           buff.length=req->scgi_content_length;
            while ( (*p)!=0)  { *(t++)=*(p++); }
        /*  set up ruser */
           p=req->remote_user;
           if (p==0) { printf("Defaulting user to unknown"); p="unknown";}
           t =ruser.data;
           ruser.type=1;
           ruser.length=strlen(p);
           while ( (*p)!=0)  { *(t++)=*(p++); }
        /* set up func */
           p=req->request_uri+5; // +5 to skip /tau.
           t =func.data;
           func.type=1;
           func.length=strlen(p);
           while ( (*p)!=0)  { *(t++)=*(p++); }
        
         /*echo request */
        { int jj;
          for (jj=0;jj<buff.length; jj++) printf("%c",buff.data[jj]); 
          printf("\n" );
          printf("func %s\n",req->request_uri+5);

        }
        }

  if ( ! scgi_sendtau( req, step("mainZcoreZUTF8ZUTF8ZUTF8",&ruser,&func,&buff) ))
       /* if ( !scgi_write( req,  "Status: 200 OK\r\n"
                                "Content-Type: text/plain\r\n\r\n"
                                "Hello World!" ) )*/
        {
          printf( "Our response could not be sent, we couldn't allocate the necessary RAM.\n" );
        }
        else
          if ( dead == 1 )
            printf(	"Oh my, something went wrong!\n"
			"The connection was killed by the SCGI Library when we tried to send the response.\n" );

        /*
         * From here on, helloworld.c forgets about the request (though the library itself still remembers it)
         * so we can relieve the library from having to maintain the req->dead
         */
        if ( !dead )
          req->dead = NULL;
        printf("finished send");
        printf("\n");
      }
      else
        break;
    }
  }
}



int main(int argc, char **argv)    {   int i=0; 
       struct str2 myarg;
       // printf("argc %d\n",argc);
       if (argc ==1)  {
          // if no argument is supplied run the server
           inittau(1);
           return serverloop();
       }
       // if there is an arg then compile the library
       inittau(0);
       while( argv[1][i] != 0 ) { myarg.data[i]=argv[1][i];i++ ;}
       if (argc > 2){ int j=0;  myarg.data[i++]=' '; 
            while( argv[2][j] != 0 ) { myarg.data[i]=argv[2][j++];i++ ;}
        }
        if (argc > 3){ int j=0;  myarg.data[i++]=' '; 
            while( argv[3][j] != 0 ) { myarg.data[i]=argv[3][j++];i++ ;}
        }
    
       myarg.length=i;
       myarg.type =1;
       return step("mainZmainZintzseq",&myarg,&myarg,&myarg);
     }




