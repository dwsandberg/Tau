/* A CGI (Common Gateway Interface) for writing files */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <fcntl.h>


/* Handle errors by printing a plain text message. */

static void cgi_fail (const char * message)
{
    printf ("Content-Type: text/plain\n\n" );
    printf ("%s\n", message);
    exit (0);
}

#define BUFFER_SIZE 1000

int 
main ()
{   
     int content_length=atoi(getenv("CONTENT_LENGTH"));
     char *Root=getenv("DOCUMENT_ROOT");
     char *query=getenv("QUERY_STRING");
     char filename[300];
     strcpy(filename,Root);
     strcat(filename,"/");
     strcat(filename,query);
     // check for illegal file name -- relative paths cannot be used  
     char *p;
     for(p=filename;*p!=0;p++) 
       if (  (*p=='.') && ( *(p+1)=='/' ||   *(p+1)=='\\' ))
         cgi_fail("illegal file name"); 
       else if (*p=='~' || (*p==':' )  ) cgi_fail("illegal file name"); 
     // open the file
     FILE   *fp = fopen(filename, "w"); 
     if ( fp <= 0) cgi_fail("fail open");
         printf ("Content-Type: text/html\n\n here" );
     printf("filename:%s <br> content_length:%d",filename,content_length);
  
  char buffer[BUFFER_SIZE];         
     int size=content_length;
     while (size > 0)   {
       int sz= size > BUFFER_SIZE ? BUFFER_SIZE:size;
         printf(" %lu",   fread(buffer, 1,sz,   stdin));      
       printf(" %lu",     fwrite(buffer,1,sz,   fp));
      size-=BUFFER_SIZE;
       }
       
     printf("%d",    fclose(fp));
       int f =open(  filename,O_RDWR);
        
        fchmod(f, S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP );
                  
     return 0;
}