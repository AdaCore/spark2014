/*****************************************************************************
 *                                                                           *
 *                            GNATPROVE COMPONENTS                           *
 *                                                                           *
 *                           S E M A P H O R E S _ C                         *
 *                                                                           *
 *                            C Implementation file                          *
 *                                                                           *
 *                      Copyright (C) 2019-2021, AdaCore                     *
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

#ifndef _WIN32

#include <fcntl.h>
#include <semaphore.h>
#include <stdio.h>
#include <stdlib.h>

sem_t* create_semaphore (const char *name, unsigned int init) {
  sem_t* r = sem_open (name, O_CREAT | O_EXCL, 0600, init);
  if (r == SEM_FAILED) {
    perror("failed to create semaphore");
    exit(1);
  }
  return r;
}

sem_t* open_semaphore (const char *name) {
  sem_t* r = sem_open (name, 0);
  if (r == SEM_FAILED) {
    perror("failed to open semaphore");
    exit(1);
  }
  return r;
}

void close_semaphore (sem_t *s) {
  if (sem_close(s) == -1) {
    perror("failed to close semaphore");
    exit(1);
  }
}

void wait_semaphore (sem_t *s) {
  if (sem_wait(s) == -1) {
    perror("failed to wait for semaphore");
    exit(1);
  }
}

void release_semaphore (sem_t *s) {
  if (sem_post(s) == -1) {
    perror("failed to release semaphore");
    exit(1);
  }
}

void delete_semaphore (const char *name) {
  if (sem_unlink(name) == -1) {
    //  ignore errors of deleting on purpose
  }
}

#else

#include <stdio.h>
#include <stdlib.h>
#include <windows.h>

HANDLE create_semaphore (const char *name, unsigned int init) {
  HANDLE r = CreateSemaphore(NULL, init, init, name);
  if (r == NULL) {
    printf("failed to create semaphore");
    exit(1);
  }
  return r;
}

HANDLE open_semaphore (const char *name) {
  HANDLE r = OpenSemaphore(SEMAPHORE_ALL_ACCESS, FALSE, name);
  if (r == NULL) {
    printf("failed to open semaphore\n");
    exit(1);
  }
  return r;
}

void close_semaphore (HANDLE s) {
  if (!CloseHandle(s)) {
    printf("failed to close semaphore\n");
    exit(1);
  }
}

void wait_semaphore (HANDLE s) {
  DWORD waitresult = WaitForSingleObject(s, INFINITE);
  if (waitresult != WAIT_OBJECT_0) {
    printf("failed to wait for semaphore\n");
    exit(1);
  }
}

void release_semaphore (HANDLE s) {
  if (!ReleaseSemaphore(s, 1, NULL)) {
    printf("failed to release semaphore\n");
    exit(1);
  }
}

void delete_semaphore (const char *name) {
  //  On windows, semaphores can't be deleted and go away when the last process
  //  has closed the semaphore. We do a no-op here.
  ;
}

#endif
