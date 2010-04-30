/* This file contains the C routines or variables which are defined in 
   some GCC source (and hence not available when compiling here). */

/* Originally defined in GCC's toplev.c. GNAT uses this flag to
   determine whether stack checking is enabled on the target (controls
   allocation strategy for large objects in certain cases). */
int flag_stack_check = 0;

/*  Originally defined in GCC's toplev.c. */
int optimize = 0;
int optimize_size = 0;

/* Originally defined in toplev.c, used in exp_cg.adb. */
void *callgraph_info_file = (void *)0;

/* Originally defined in GCC's prefix.c. We need a dummy
   update_path and set_std_prefix for osint.adb. */
void
set_std_prefix (char *path, int len)
{
}

char *
update_path (char *path, char *key)
{
  return path;
}

extern int sigreturn (void *uc, int flavour)
{
/* To work around Mac OS X 10.5/10.6 incompatibility */
}
