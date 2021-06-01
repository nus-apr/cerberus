#include "config.h"
#ifdef HAVE_FASTCGI_FASTCGI_H
#include <fastcgi/fcgi_stdio.h>
#else
#include <fcgi_stdio.h>
#endif
#include <stdlib.h>
#include <unistd.h>
#include <string.h>

int main () {
	int num_requests = 2;
	
	while (num_requests > 0 && FCGI_Accept() >= 0) {
		char* p = NULL;
		char* doc_root = NULL;
		char fname[4096];
		char* pfname = (char *)fname;

		doc_root = getenv("DOCUMENT_ROOT");
		p = getenv("QUERY_STRING");

		if (NULL != p && NULL != doc_root) {
			snprintf(pfname, sizeof(fname), "%s/phpinfo.php", doc_root);
			if (0 == strcmp(p, "lf")) {
				printf("Status: 200 OK\n\n");
			} else if (0 == strcmp(p, "crlf")) {
				printf("Status: 200 OK\r\n\r\n");
			} else if (0 == strcmp(p, "slow-lf")) {
				printf("Status: 200 OK\n");
				fflush(stdout);
				printf("\n");
			} else if (0 == strcmp(p,"slow-crlf")) {
				printf("Status: 200 OK\r\n");
				fflush(stdout);
				printf("\r\n");
			} else if (0 == strcmp(p,"x-lighttpd-send-file")) {
				printf("Status: 200 OK\r\n");
				printf("X-LIGHTTPD-send-file: %s\r\n", pfname);
				printf("\r\n");
			} else if (0 == strcmp(p,"xsendfile")) {
				printf("Status: 200 OK\r\n");
				printf("X-Sendfile: %s\r\n", pfname);
				printf("\r\n");
			} else if (0 == strcmp(p,"xsendfile-mixed-case")) {
				printf("Status: 200 OK\r\n");
				printf("X-SeNdFiLe: %s\r\n", pfname);
				printf("\r\n");
			} else if (0 == strcmp(p, "die-at-end")) {
				printf("Status: 200 OK\r\n\r\n");
				num_requests--;
			} else {
				printf("Status: 200 OK\r\n\r\n");
			}
		} else {
			printf("Status: 500 Internal Foo\r\n\r\n");
		}
		 
		printf("test123");
	}
	
	return 0;
}
