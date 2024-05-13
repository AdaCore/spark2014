/*****************************************************************************
 *                                                                           *
 *                            GNATPROVE COMPONENTS                           *
 *                                                                           *
 *                               C O L O R S _ C                             *
 *                                                                           *
 *                            C Implementation file                          *
 *                                                                           *
 *                      Copyright (C) 2022-2024, AdaCore                     *
 *                                                                           *
 * gnatprove is  free  software;  you can redistribute it and/or  modify it  *
 * under terms of the  GNU General Public License as published  by the Free  *
 * Software  Foundation;  either version 3,  or (at your option)  any later  *
 * version.  gnatprove is distributed  in the hope that  it will be useful,  *
 * but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN-  *
 * TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public  *
 * License for  more details.  You should have  received  a copy of the GNU  *
 * General Public License  distributed with  gnatprove;  see file COPYING3.  *
 * If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the  *
 * license.                                                                  *
 *                                                                           *
 * gnatprove is maintained by AdaCore (http://www.adacore.com)               *
 *                                                                           *
 *****************************************************************************/

#ifdef _WIN32
#include <windows.h>
#include <io.h>
#else
#include <unistd.h>
#include <stdio.h>
#endif

// Return 0 on failure and non-zero on success

int stdout_set_colors() {
#ifdef _WIN32
   HANDLE hOut = GetStdHandle(STD_OUTPUT_HANDLE);
   if (hOut == INVALID_HANDLE_VALUE) return 0;

   DWORD dwMode;
   if (!GetConsoleMode(hOut, &dwMode)) return 0;

   dwMode |= ENABLE_VIRTUAL_TERMINAL_PROCESSING;
   if (!SetConsoleMode(hOut, dwMode)) return 0;
   return 1;
#else
   return isatty(fileno(stdout));
#endif
}
