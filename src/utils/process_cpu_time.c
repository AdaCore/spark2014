/*****************************************************************************
 *                                                                           *
 *                            GNAT2WHY COMPONENTS                           *
 *                                                                           *
 *                     P R O C E S S _ C P U _ T I M E                      *
 *                                                                           *
 *                            C Implementation file                          *
 *                                                                           *
 *                     Copyright (C) 2026-2026, AdaCore                      *
 *                                                                           *
 * gnat2why is  free  software;  you can redistribute  it and/or  modify it  *
 * under terms of the  GNU General Public License as published  by the Free  *
 * Software  Foundation;  either version 3,  or (at your option)  any later  *
 * version.  gnat2why is distributed  in the hope that  it will be  useful,  *
 * but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN-  *
 * TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public  *
 * License for  more details.  You should have  received  a copy of the GNU  *
 * General Public License  distributed with  gnat2why;  see file COPYING3.  *
 * If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the  *
 * license.                                                                  *
 *                                                                           *
 *****************************************************************************/

/* Returns total process CPU time (user + system) via output parameters sec
   and nsec (seconds and nanoseconds).  On POSIX systems this uses
   clock_gettime(CLOCK_PROCESS_CPUTIME_ID); on Windows it uses
   GetProcessTimes.  The result is suitable for measuring elapsed CPU work and
   excludes time spent blocked waiting for child processes. */

#ifndef _WIN32

#include <time.h>

void process_cpu_time (long long *sec, long *nsec)
{
  struct timespec ts;
  clock_gettime (CLOCK_PROCESS_CPUTIME_ID, &ts);
  *sec  = (long long) ts.tv_sec;
  *nsec = (long) ts.tv_nsec;
}

#else

#include <windows.h>

void process_cpu_time (long long *sec, long *nsec)
{
  FILETIME creation, exit, kernel, user;
  ULARGE_INTEGER k, u;
  ULONGLONG total;
  GetProcessTimes (GetCurrentProcess (), &creation, &exit, &kernel, &user);
  k.LowPart  = kernel.dwLowDateTime;
  k.HighPart = kernel.dwHighDateTime;
  u.LowPart  = user.dwLowDateTime;
  u.HighPart = user.dwHighDateTime;
  /* FILETIME units are 100 nanoseconds; convert to seconds + nanoseconds */
  total = k.QuadPart + u.QuadPart;
  *sec  = (long long) (total / 10000000);
  *nsec = (long) ((total % 10000000) * 100);
}

#endif
