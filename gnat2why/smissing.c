/****************************************************************************
 *                                                                          *
 *                          GNAT COMPILER COMPONENTS                        *
 *                                                                          *
 *                              j m i s s i n g                             *
 *                                                                          *
 *                      Copyright (C) 1998-2014, AdaCore                    *
 *                                                                          *
 * GNAT is free software;  you can  redistribute it  and/or modify it under *
 * terms of the  GNU General Public License as published  by the Free Soft- *
 * ware  Foundation;  either version 3,  or (at your option) any later ver- *
 * sion.  GNAT is distributed in the hope that it will be useful, but WITH- *
 * OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY *
 * or FITNESS FOR A PARTICULAR PURPOSE.                                     *
 *                                                                          *
 * As a special exception under Section 7 of GPL version 3, you are granted *
 * additional permissions described in the GCC Runtime Library Exception,   *
 * version 3.1, as published by the Free Software Foundation.               *
 *                                                                          *
 * You should have received a copy of the GNU General Public License and    *
 * a copy of the GCC Runtime Library Exception along with this program;     *
 * see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see    *
 * <http://www.gnu.org/licenses/>.                                          *
 *                                                                          *
 ****************************************************************************/

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

/* Originally defined in misc.c.  */
unsigned int save_argc = 0;
const char **save_argv = (const char **)0;

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
