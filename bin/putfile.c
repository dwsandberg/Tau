/* A CGI (Common Gateway Interface) for writing files */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

/* Print a basic HTTP header. */

static void
print_http_header (const char * content_type)
{
    printf ("Content-Type: %s\n\n", content_type);
}

/* Handle errors by printing a plain text message. */

static void cgi_fail (const char * message)
{
    print_http_header ("text/plain");
    printf ("%s\n", message);
    exit (0);
}

#define BUFFER_SIZE 1000

int 
main ()
{    print_http_header ("text/html");
     int content_length=atoi(getenv("CONTENT_LENGTH"));
     char *Root=getenv("DOCUMENT_ROOT");
     char *query=getenv("QUERY_STRING");
     char buffer[BUFFER_SIZE];
     strcpy(buffer,Root);
     strcat(buffer,"/");
     strcat(buffer,query);
     // check for illegal file name -- relative paths cannot be used  
     char *p;
     for(p=buffer;*p!=0;p++) 
       if (  (*p=='.') && ( *(p+1)=='/' ||   *(p+1)=='\\' ))
         cgi_fail("illegal file name"); 
       else if (*p=='~' || (*p==':' )  ) cgi_fail("illegal file name"); 
     // open the file
     FILE   *fp = fopen(buffer, "w"); 
     if ( fp < 0) cgi_fail("fail open");
     printf("filename:%s <br>",buffer);
         
     int size=content_length;
     while (size > 0)   {
       int sz= size > BUFFER_SIZE ? BUFFER_SIZE:size;
       printf("%lu",   fread(buffer, 1,sz,   stdin));      
       printf("%lu",     fwrite(buffer,1,sz,   fp));
       size-=BUFFER_SIZE;
       }
     printf("%d",    fclose(fp));
     return 0;
}