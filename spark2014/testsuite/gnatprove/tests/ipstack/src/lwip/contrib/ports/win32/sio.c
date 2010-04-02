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
 */

#include <lwip/opt.h>
#include <lwip/sys.h>
#include <lwip/sio.h>

#include <stdio.h>
#include <stdarg.h>

#include <windows.h>

static int sio_abort=0;

/* \\.\pipe\lwip0 */
/* pppd /dev/ttyS0 logfile mylog debug nocrtscts local noauth noccp ms-dns 212.27.54.252 192.168.0.4:192.168.0.5
 */

/**
 * SIO_DEBUG: Enable debugging for SIO.
 */
#ifndef SIO_DEBUG
#define SIO_DEBUG    LWIP_DBG_OFF
#endif

/**
* Open serial port entry point from serial protocol (slipif, pppif)
* @param devnum the device number to use, i.e. ttySx, comx:, etc. there x = devnum
* @return psio struct, contains sio instance data, use when calling sio functions
*/
sio_fd_t sio_open(u8_t devnum)
{ HANDLE hPipe = INVALID_HANDLE_VALUE;
  CHAR   szPipeName[256];
  LWIP_DEBUGF( SIO_DEBUG, ("sio_open(%lu)\n", (DWORD)devnum));
  sprintf( szPipeName, "\\\\.\\pipe\\lwip%lu", (DWORD)(devnum));
  hPipe = CreateFile(szPipeName, GENERIC_READ | GENERIC_WRITE, 0, NULL, OPEN_EXISTING, 0, NULL);
  if (hPipe != INVALID_HANDLE_VALUE) {
    sio_abort=0;
    FlushFileBuffers(hPipe);
    return (sio_fd_t)(hPipe);
  }
  return NULL;
}

/**
 * Write a char to output data stream
 * @param num char to write to output stream
 * @param psio struct, contains sio instance data, given by sio_open
 */
void sio_send(u8_t num, sio_fd_t psio)
{ DWORD dwNbBytesWritten = 0;
  LWIP_DEBUGF( SIO_DEBUG, ("sio_send(%lu)\n", (DWORD)num));
  while ((!WriteFile( (HANDLE)(psio), &num, 1, &dwNbBytesWritten, NULL)) || (dwNbBytesWritten<1));
  return;
}

/**
 * Read a char from incoming data stream, this call blocks until data has arrived
 * @param psio siostatus struct, contains sio instance data, given by sio_open
 * @return char read from input stream
 */
u8_t sio_recv(sio_fd_t psio)
{ DWORD dwNbBytesReadden = 0;
  u8_t byte = 0;
  LWIP_DEBUGF( SIO_DEBUG, ("sio_recv()\n"));
  while ((sio_abort==0) && ((!ReadFile( (HANDLE)(psio), &byte, 1, &dwNbBytesReadden, NULL)) || (dwNbBytesReadden<1)));
  LWIP_DEBUGF( SIO_DEBUG, ("sio_recv()=%lu\n", (DWORD)byte));
  return byte;
}

u32_t sio_read(sio_fd_t psio, u8_t * data, u32_t len)
{ DWORD dwNbBytesReadden = 0;
  LWIP_DEBUGF( SIO_DEBUG, ("sio_read()...\n"));
  ReadFile( (HANDLE)(psio), data, len, &dwNbBytesReadden, NULL);
  LWIP_DEBUGF( SIO_DEBUG, ("sio_read()=%lu bytes\n", dwNbBytesReadden));
  return dwNbBytesReadden;
}

u32_t sio_write(sio_fd_t psio, u8_t * data, u32_t len)
{ DWORD dwNbBytesWritten = 0;
  LWIP_DEBUGF( SIO_DEBUG, ("sio_write()...\n"));
  WriteFile( (HANDLE)(psio), data, len, &dwNbBytesWritten, NULL);
  LWIP_DEBUGF( SIO_DEBUG, ("sio_write()=%lu bytes\n", dwNbBytesWritten));
  return dwNbBytesWritten;
}

void sio_read_abort(sio_fd_t psio)
{ LWIP_UNUSED_ARG(psio);
  LWIP_DEBUGF( SIO_DEBUG, ("sio_read_abort() !!!!!...\n"));
  sio_abort=1;
  return;
}

void ppp_trace( int level, const char *format, ...)
{ int len;
  char buffer[1024];
  va_list argList;

  LWIP_UNUSED_ARG(level);

  va_start  ( argList, format);
  len=vsprintf( buffer, format, argList);
  buffer[len-1]='\0';
  va_end    ( argList);
  printf("%s\n", buffer);
}

int snprintf( char *buffer, size_t count, const char *format, ...)
{ int len;
  va_list argList;

  LWIP_UNUSED_ARG(count);

  va_start  ( argList, format);
  len=vsprintf( buffer, format, argList);
  buffer[len-1]='\0';
  va_end    ( argList);
  return len;
}
