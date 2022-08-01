/*****************************************************************************
 *                                                                           *
 *                            GNATPROVE COMPONENTS                           *
 *                                                                           *
 *                           S E M A P H O R E S _ C                         *
 *                                                                           *
 *                            C Implementation file                          *
 *                                                                           *
 *                      Copyright (C) 2019-2022, AdaCore                     *
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

#include <sys/types.h>
#include <sys/ipc.h>
#include <sys/sem.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

// Compute the path for a given semaphore name. The caller has the
// responsibility to free the memory.
char* name_to_path(const char *name) {
  // Length of name + 5 chars for "/tmp/" + null terminator
  char* sem_name = malloc (strlen (name) + 6);
  strcpy (sem_name, "/tmp/");
  strcat (sem_name, name);
  return sem_name;
}

// Compute the key for a given name
key_t name_to_key (const char *name) {
  key_t result;
  // We use an arbitrary project id
  result = ftok (name, 10);
  if (result == -1) {
    perror("failed to generate IPC key");
    exit(1);
  }
  return result;
}

int* create_semaphore (const char *name, unsigned int init) {
  // Taken from semctl man page
  union semun {
       int              val;
       struct semid_ds *buf;
       unsigned short  *array;
       struct seminfo  *__buf;
  } sem_attr;
  int result;
  int* sem_result;
  char* sem_name = name_to_path(name);
  int fd = open(sem_name, O_CREAT | O_EXCL, 0644);
  if (fd == -1) {
    perror("failed to create semaphore file");
    exit(1);
  }
  if (close(fd) == -1) {
    perror("failed to close semaphore file");
    exit(1);
  }
  key_t s_key = name_to_key (sem_name);
  free(sem_name);
  result = semget (s_key, 1, 0660 | IPC_CREAT | IPC_EXCL);
  if (result == -1) {
    perror("failed to create semaphore");
    exit(1);
  }
  sem_attr.val = init;
  if (semctl (result, 0, SETVAL, sem_attr) == -1) {
    perror("failed to set initial value of semaphore");
    exit(1);
  }
  sem_result = malloc(sizeof(int));
  *sem_result = result;
  return sem_result;
}

int* open_semaphore (const char *name) {
  int result;
  int* sem_result;
  char* sem_name = name_to_path(name);
  key_t s_key = name_to_key (sem_name);
  free(sem_name);
  result = semget (s_key, 0, 0);
  if (result == -1) {
    perror("failed to open semaphore");
    exit(1);
  }
  sem_result = malloc(sizeof(int));
  *sem_result = result;
  return sem_result;
}

void close_semaphore (int* s) {
  free(s);
}

void wait_semaphore (int* s) {
  struct sembuf asem [1];
  asem[0].sem_num = 0;
  asem[0].sem_op = -1;
  // ??? Do we want to use SEM_UNDO here?
  asem[0].sem_flg = 0;
  if (semop (*s, asem, 1) == -1) {
    perror ("failed to decrease semaphore");
    exit (1);
  }
}

void release_semaphore (int* s) {
  struct sembuf asem [1];
  asem[0].sem_num = 0;
  asem[0].sem_op = 1;
  asem[0].sem_flg = 0;
  if (semop (*s, asem, 1) == -1) {
    perror ("failed to increase semaphore");
    exit (1);
  }
}

void delete_semaphore (const char *name) {
  char* sem_name = name_to_path(name);
  struct stat stat_rec;
  key_t s_key;
  int sem;
  if(stat(sem_name, &stat_rec) == 0) {
    s_key = name_to_key (sem_name);
    sem = semget(s_key, 0, 0);

    if (sem == -1) {
      perror("failed to retrieve semaphore for deletion");
      exit(1);
    }

    if (semctl (sem, 0, IPC_RMID) == -1) {
      // Ignore errors of deleting on purpose
    }
    if (unlink (sem_name) == -1) {
      // Ignore errors of deleting on purpose
    }
    free(sem_name);
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
