#include "ctm.h"

/*---------------------------------------------------------------------------*/
/* Pass2 -- Validate the incomming CTM-file.
 */

int
Pass2(FILE *fd)
{
    u_char *p,*q;
    MD5_CTX ctx;
    int i,j,sep,cnt;
    u_char *trash=0,*name=0;
    struct CTM_Syntax *sp;
    struct stat st;

    if(Verbose>3) 
	printf("Pass2 -- Checking if CTM-patch will apply\n");
    MD5Init (&ctx);

    GETFIELD(p,' '); if(strcmp("CTM_BEGIN",p)) WRONG
    GETFIELD(p,' '); if(strcmp(Version,p)) WRONG
    GETFIELD(p,' '); if(strcmp(Name,p)) WRONG
    /* XXX Lookup name in /etc/ctm,conf, read stuff */
    GETFIELD(p,' '); if(strcmp(Nbr,p)) WRONG
    /* XXX Verify that this is the next patch to apply */
    GETFIELD(p,' '); if(strcmp(TimeStamp,p)) WRONG
    GETFIELD(p,'\n'); if(strcmp(Prefix,p)) WRONG
    /* XXX drop or use ? */

    for(;;) {
	if(trash)	{Free(trash), trash = 0;}
	if(name)	{Free(name), name = 0;}
	cnt = -1;

	GETFIELD(p,' ');

	if (p[0] != 'C' || p[1] != 'T' || p[2] != 'M') WRONG

	if(!strcmp(p+3,"_END"))
	    break;

	for(sp=Syntax;sp->Key;sp++)
	    if(!strcmp(p+3,sp->Key))
		goto found;
	WRONG
    found:
	for(i=0;(j = sp->List[i]);i++) {
	    if (sp->List[i+1] && (sp->List[i+1] & CTM_F_MASK) != CTM_F_Bytes)
		sep = ' ';
	    else
		sep = '\n';

	    switch (j & CTM_F_MASK) {
		case CTM_F_Name:
		    GETFIELDCOPY(name,sep);
		    /* XXX Check DR DM rec's for parent-dir */
		    if(j & CTM_Q_Name_New) {
			/* XXX Check DR FR rec's for item */
			if(-1 != stat(name,&st)) {
			    fprintf(stderr,"  %s: %s exists.\n",sp->Key,name);
			}
			break;
		    }
		    if(-1 == stat(name,&st)) {
			fprintf(stderr,"  %s: %s doesn't exists.\n",
			    sp->Key,name);
			break;
		    } 
		    if (j & CTM_Q_Name_Dir) {
			if((st.st_mode & S_IFMT) != S_IFDIR)
			    fprintf(stderr,
				"  %s: %s exist, but isn't dir.\n",
				sp->Key,name);
			break;
		    } 
		    if (j & CTM_Q_Name_File) {
			if((st.st_mode & S_IFMT) != S_IFREG)
			    fprintf(stderr,
				"  %s: %s exist, but isn't file.\n",
				sp->Key,name);
			break;
		    }
		    break;
		case CTM_F_Uid:
		case CTM_F_Gid:
		case CTM_F_Mode:
		    GETFIELD(p,sep);
		    break;
		case CTM_F_MD5:
		    if(!name) WRONG
		    GETFIELD(p,sep);
		    if((st.st_mode & S_IFMT) == S_IFREG) {
			if(j & CTM_Q_MD5_Before && strcmp(MD5File(name),p)) {
			    fprintf(stderr,"  %s: %s md5 mismatch.\n",sp->Key,name);
			}
		    }
		    break;
		case CTM_F_Count:
		    GETBYTECNT(cnt,sep);
		    break;
		case CTM_F_Bytes:
		    if(cnt < 0) WRONG
		    GETDATA(trash,cnt);
		    p = MD5Data(trash,cnt);
		    break;
		default: WRONG
	    }
        }
    }
    q = MD5End (&ctx);
    GETFIELD(p,'\n');			/* <MD5> */
    if(strcmp(q,p)) WRONG
    if (-1 != getc(fd)) WRONG
    return 0;
}
