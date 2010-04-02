/*
 * Copyright (c) 2001-2003 Swedish Institute of Computer Science.
 * All rights reserved. 
 * 
 * Redistribution and use in source and binary forms, with or without modification, 
 * are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 * 3. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission. 
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR IMPLIED 
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF 
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT 
 * SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, 
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT 
 * OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS 
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN 
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING 
 * IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY 
 * OF SUCH DAMAGE.
 *
 * This file is part of the lwIP TCP/IP stack.
 * 
 * Author: Adam Dunkels <adam@sics.se>
 *         Simon Goldschmidt
 *
 */

#include <stdlib.h>
#include <stdio.h> /* sprintf() for task names */

#include <windows.h>
#include <time.h>

#include <lwip/opt.h>
#include <lwip/stats.h>
#include <lwip/debug.h>
#include <lwip/sys.h>

/* These functions are used from NO_SYS also, for precise timer triggering */
LARGE_INTEGER freq, sys_start_time;

void sys_init_timing()
{
  QueryPerformanceFrequency(&freq);
  QueryPerformanceCounter(&sys_start_time);
}

static LONGLONG sys_get_ms_longlong()
{
  LONGLONG ret;
  LARGE_INTEGER now;
  QueryPerformanceCounter(&now);
  ret = now.QuadPart-sys_start_time.QuadPart;
  return (u32_t)(((ret)*1000)/freq.QuadPart);
}

u32_t sys_now()
{
  return sys_get_ms_longlong();
}

#if !NO_SYS

#define MAX_QUEUE_ENTRIES 100

struct threadlist {
  struct sys_timeouts timeouts;
  DWORD id;
  struct threadlist *next;
};

struct lwip_mbox {
  HANDLE sem;
  void* q_mem[MAX_QUEUE_ENTRIES];
  u32_t head, tail;
};

struct threadlist *lwip_win32_threads = NULL;
CRITICAL_SECTION critSec;

void InitSysArchProtect()
{
  InitializeCriticalSection(&critSec);
}
u32_t sys_arch_protect()
{
  EnterCriticalSection(&critSec);
  return 0;
}
void sys_arch_unprotect(u32_t pval)
{
  LWIP_UNUSED_ARG(pval);
  LeaveCriticalSection(&critSec);
}
void do_sleep(int ms)
{
  Sleep(ms);
}

void sys_init(void)
{
  sys_init_timing();
  InitSysArchProtect();
}

sys_sem_t sys_sem_new(u8_t count)
{
  HANDLE new_sem = NULL;
  new_sem = CreateSemaphore(0, count, 100000, 0);
  LWIP_ASSERT("Error creating semaphore", new_sem != NULL);
  if(new_sem != NULL) {
#if LWIP_STATS
    lwip_stats.sys.sem.used++;
    LWIP_ASSERT("sys_sem_new() counter overflow", lwip_stats.sys.sem.used != 0 );
    if (lwip_stats.sys.sem.used > lwip_stats.sys.sem.max) {
      lwip_stats.sys.sem.max = lwip_stats.sys.sem.used;
    }
#endif /* LWIP_STATS */
    return new_sem;
  }
   
  /* failed to allocate memory... */
#if LWIP_STATS
  lwip_stats.sys.sem.err++;
#endif /* LWIP_STATS */
  return SYS_SEM_NULL;
}

void sys_sem_free(sys_sem_t sem)
{
  /* parameter check */
  LWIP_ASSERT("sem != NULL", sem != NULL);
  LWIP_ASSERT("sem != INVALID_HANDLE_VALUE", sem != INVALID_HANDLE_VALUE);
  CloseHandle(sem);

#if LWIP_STATS
  lwip_stats.sys.sem.used--;
  LWIP_ASSERT("sys_sem_free() closed more than created", lwip_stats.sys.sem.used != (u16_t)-1);
#endif /* LWIP_STATS */
}

u32_t sys_arch_sem_wait(sys_sem_t sem, u32_t timeout)
{
  DWORD ret;
  LONGLONG starttime, endtime;
  LWIP_ASSERT("sem != NULL", sem != NULL);
  LWIP_ASSERT("sem != INVALID_HANDLE_VALUE", sem != INVALID_HANDLE_VALUE);
  if(!timeout)
  {
    /* wait infinite */
    starttime = sys_get_ms_longlong();
    ret = WaitForSingleObject(sem, INFINITE);
    LWIP_ASSERT("Error waiting for mutex", ret == WAIT_OBJECT_0);
    endtime = sys_get_ms_longlong();
    /* return the time we waited for the sem */
    return (u32_t)(endtime - starttime);
  }
  else
  {
    int ret;
    starttime = sys_get_ms_longlong();
    ret = WaitForSingleObject(sem, timeout);
    LWIP_ASSERT("Error waiting for mutex", (ret == WAIT_OBJECT_0) || (ret == WAIT_TIMEOUT));
    if(ret == WAIT_OBJECT_0)
    {
      endtime = sys_get_ms_longlong();
      /* return the time we waited for the sem */
      return (u32_t)(endtime - starttime);
    }
    else
    {
      /* timeout */
      return SYS_ARCH_TIMEOUT;
    }
  }
}

void sys_sem_signal(sys_sem_t sem)
{
  DWORD ret;
  LWIP_ASSERT("sem != NULL", sem != NULL);
  LWIP_ASSERT("sem != INVALID_HANDLE_VALUE", sem != INVALID_HANDLE_VALUE);
  ret = ReleaseSemaphore(sem, 1, NULL);
  LWIP_ASSERT("Error releasing mutex", ret != 0);
}

struct sys_timeouts *sys_arch_timeouts(void)
{
  struct sys_timeouts *ret = NULL;
  struct threadlist *t, *new_thread;
  SYS_ARCH_DECL_PROTECT(lev);
  DWORD threadID;

  threadID = GetCurrentThreadId();
  SYS_ARCH_PROTECT(lev);
  for(t = lwip_win32_threads; t != NULL; t = t->next)
  {
    if(t->id == threadID)
    {
      ret = &(t->timeouts);
      SYS_ARCH_UNPROTECT(lev);
      return ret;
    }
  }
  new_thread = (struct threadlist*)malloc(sizeof(struct threadlist));
  LWIP_ASSERT("new_thread != NULL", new_thread != NULL);
  if(new_thread != NULL) {
    OutputDebugString("First call to sys_arch_timeouts for thread");
    new_thread->next = lwip_win32_threads;
    lwip_win32_threads = new_thread;
    new_thread->id = threadID;
    new_thread->timeouts.next = NULL;
    ret = &(new_thread->timeouts);
    SYS_ARCH_UNPROTECT(lev);
    return ret;
  }
  SYS_ARCH_UNPROTECT(lev);
  LWIP_ASSERT("should not come here", 0);
  return 0;
}

sys_thread_t sys_thread_new(char *name, void (* function)(void *arg), void *arg, int stacksize, int prio)
{
  struct threadlist *new_thread;
  HANDLE h;
  SYS_ARCH_DECL_PROTECT(lev);

  LWIP_UNUSED_ARG(name);
  LWIP_UNUSED_ARG(stacksize);
  LWIP_UNUSED_ARG(prio);

  new_thread = (struct threadlist*)malloc(sizeof(struct threadlist));
  LWIP_ASSERT("new_thread != NULL", new_thread != NULL);
  if(new_thread != NULL) {
    SYS_ARCH_PROTECT(lev);
    new_thread->next = lwip_win32_threads;
    lwip_win32_threads = new_thread;
    new_thread->timeouts.next = NULL;

    h = CreateThread(0, 0, (LPTHREAD_START_ROUTINE)function, arg, 0, &(new_thread->id));
    LWIP_ASSERT("h != 0", h != 0);
    LWIP_ASSERT("h != -1", h != INVALID_HANDLE_VALUE);

    SYS_ARCH_UNPROTECT(lev);
    return new_thread->id;
  }
  return 0;
}

sys_mbox_t sys_mbox_new(int size)
{
  struct lwip_mbox *new_mbox;

  LWIP_UNUSED_ARG(size);

  new_mbox = (struct lwip_mbox*)malloc(sizeof(struct lwip_mbox));
  LWIP_ASSERT("new_mbox != NULL", new_mbox != NULL);
  if(new_mbox == NULL) {
#if LWIP_STATS
    lwip_stats.sys.mbox.err++;
#endif /* LWIP_STATS */
    return SYS_SEM_NULL;
  }
  new_mbox->sem = CreateSemaphore(0, 0, MAX_QUEUE_ENTRIES, 0);
  LWIP_ASSERT("Error creating semaphore", new_mbox->sem != NULL);
  if(new_mbox->sem == NULL) {
#if LWIP_STATS
    lwip_stats.sys.mbox.err++;
#endif /* LWIP_STATS */
    free(new_mbox);
    new_mbox = NULL;
    return SYS_SEM_NULL;
  }
  memset(&new_mbox->q_mem, 0, sizeof(u32_t)*MAX_QUEUE_ENTRIES);
  new_mbox->head = 0;
  new_mbox->tail = 0;
#if LWIP_STATS
  lwip_stats.sys.mbox.used++;
  LWIP_ASSERT("sys_mbox_new() counter overflow", lwip_stats.sys.mbox.used != 0 );
  if (lwip_stats.sys.mbox.used > lwip_stats.sys.mbox.max) {
    lwip_stats.sys.mbox.max = lwip_stats.sys.mbox.used;
  }
#endif /* LWIP_STATS */
  return new_mbox;
}

void sys_mbox_free(sys_mbox_t mbox)
{
  /* parameter check */
  LWIP_ASSERT("sys_mbox_free ", mbox != SYS_MBOX_NULL );
  LWIP_ASSERT("mbox->sem != NULL", mbox->sem != NULL);
  LWIP_ASSERT("mbox->sem != INVALID_HANDLE_VALUE", mbox->sem != INVALID_HANDLE_VALUE);

  CloseHandle(mbox->sem);
  free(mbox);

#if LWIP_STATS
   lwip_stats.sys.mbox.used--;
   LWIP_ASSERT( "sys_mbox_free() ", lwip_stats.sys.mbox.used!= (u16_t)-1 );
#endif /* LWIP_STATS */
}

void sys_mbox_post(sys_mbox_t q, void *msg)
{
  DWORD ret;
  SYS_ARCH_DECL_PROTECT(lev);

  /* parameter check */
  LWIP_ASSERT("sys_mbox_free ", q != SYS_MBOX_NULL );
  LWIP_ASSERT("q->sem != NULL", q->sem != NULL);
  LWIP_ASSERT("q->sem != INVALID_HANDLE_VALUE", q->sem != INVALID_HANDLE_VALUE);

  SYS_ARCH_PROTECT(lev);
  q->q_mem[q->head] = msg;
  (q->head)++;
  if (q->head >= MAX_QUEUE_ENTRIES) {
    q->head = 0;
  }
  LWIP_ASSERT("mbox is full!", q->head != q->tail);
  ret = ReleaseSemaphore(q->sem, 1, 0);
  LWIP_ASSERT("Error releasing sem", ret != 0);

  SYS_ARCH_UNPROTECT(lev);
}

err_t sys_mbox_trypost(sys_mbox_t q, void *msg)
{
  u32_t new_head;
  DWORD ret;
  SYS_ARCH_DECL_PROTECT(lev);

  /* parameter check */
  LWIP_ASSERT("sys_mbox_free ", q != SYS_MBOX_NULL );
  LWIP_ASSERT("q->sem != NULL", q->sem != NULL);
  LWIP_ASSERT("q->sem != INVALID_HANDLE_VALUE", q->sem != INVALID_HANDLE_VALUE);

  SYS_ARCH_PROTECT(lev);

  new_head = q->head + 1;
  if (new_head >= MAX_QUEUE_ENTRIES) {
    new_head = 0;
  }
  if (new_head == q->tail) {
    SYS_ARCH_UNPROTECT(lev);
    return ERR_MEM;
  }

  q->q_mem[q->head] = msg;
  q->head = new_head;
  LWIP_ASSERT("mbox is full!", q->head != q->tail);
  ret = ReleaseSemaphore(q->sem, 1, 0);
  LWIP_ASSERT("Error releasing sem", ret != 0);

  SYS_ARCH_UNPROTECT(lev);
  return ERR_OK;
}

u32_t sys_arch_mbox_fetch(sys_mbox_t q, void **msg, u32_t timeout)
{
  DWORD ret;
  LONGLONG starttime, endtime;
  SYS_ARCH_DECL_PROTECT(lev);

  /* parameter check */
  LWIP_ASSERT("sys_mbox_free ", q != SYS_MBOX_NULL );
  LWIP_ASSERT("q->sem != NULL", q->sem != NULL);
  LWIP_ASSERT("q->sem != INVALID_HANDLE_VALUE", q->sem != INVALID_HANDLE_VALUE);

  if (timeout == 0) {
    timeout = INFINITE;
  }
  starttime = sys_get_ms_longlong();
  if ((ret = WaitForSingleObject(q->sem, timeout)) == WAIT_OBJECT_0) {
    SYS_ARCH_PROTECT(lev);
    if(msg != NULL) {
      *msg  = q->q_mem[q->tail];
    }

    (q->tail)++;
    if (q->tail >= MAX_QUEUE_ENTRIES) {
      q->tail = 0;
    }
    SYS_ARCH_UNPROTECT(lev);
    endtime = sys_get_ms_longlong();
    return (u32_t)(endtime - starttime);
  }
  else
  {
    LWIP_ASSERT("Error waiting for sem", ret == WAIT_TIMEOUT);
    if(msg != NULL) {
      *msg  = NULL;
    }

    return SYS_ARCH_TIMEOUT;
  }
}

u32_t sys_arch_mbox_tryfetch(sys_mbox_t q, void **msg)
{
  DWORD ret;
  SYS_ARCH_DECL_PROTECT(lev);

  /* parameter check */
  LWIP_ASSERT("sys_mbox_free ", q != SYS_MBOX_NULL );
  LWIP_ASSERT("q->sem != NULL", q->sem != NULL);
  LWIP_ASSERT("q->sem != INVALID_HANDLE_VALUE", q->sem != INVALID_HANDLE_VALUE);

  if ((ret = WaitForSingleObject(q->sem, 0)) == WAIT_OBJECT_0) {
    SYS_ARCH_PROTECT(lev);
    if(msg != NULL) {
      *msg  = q->q_mem[q->tail];
    }

    (q->tail)++;
    if (q->tail >= MAX_QUEUE_ENTRIES) {
      q->tail = 0;
    }
    SYS_ARCH_UNPROTECT(lev);
    return 0;
  }
  else
  {
    LWIP_ASSERT("Error waiting for sem", ret == WAIT_TIMEOUT);
    if(msg != NULL) {
      *msg  = NULL;
    }

    return SYS_ARCH_TIMEOUT;
  }
}
#endif /* !NO_SYS */
