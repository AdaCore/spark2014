/* Author: Magnus Ivarsson <magnus.ivarsson@volvo.com> */

/* ---------------------------------------------- */
/* --- fifo 4 unix ------------------------------ */
/* ---------------------------------------------- */
#include "netif/fifo.h"
#include "lwip/debug.h"
#include "lwip/def.h"
#include "lwip/sys.h"
#include "lwip/arch.h"
#include <unistd.h>

#ifndef TRUE
#define TRUE  1
#endif
#ifndef FALSE
#define FALSE 0
#endif


u8_t fifoGet(fifo_t * fifo) 
{
	u8_t c;

	sys_sem_wait(fifo->sem);      /* enter critical section */

	if (fifo->dataslot == fifo->emptyslot) 
	{
            fifo->getWaiting = TRUE;    /* tell putFifo to signal us when data is available */
            sys_sem_signal(fifo->sem);  /* leave critical section (allow input from serial port..) */
            sys_sem_wait(fifo->getSem); /* wait 4 data */
            sys_sem_wait(fifo->sem);    /* reenter critical section */
	}

	c = fifo->data[fifo->dataslot++];
	fifo->len--;

	if (fifo->dataslot == FIFOSIZE) 
	{
		fifo->dataslot = 0; 
	}
	sys_sem_signal(fifo->sem);    /* leave critical section */
	return c;
}


s16_t fifoGetNonBlock(fifo_t * fifo) 
{
	u16_t c;

	sys_sem_wait(fifo->sem);      /* enter critical section */

	if (fifo->dataslot == fifo->emptyslot) 
	{
            /* empty fifo */
		c = -1;
	}
	else
	{
		c = fifo->data[fifo->dataslot++];
		fifo->len--;

		if (fifo->dataslot == FIFOSIZE) 
		{
			fifo->dataslot = 0; 
		}
	}
	sys_sem_signal(fifo->sem);    /* leave critical section */
	return c;
}


void fifoPut(fifo_t * fifo, int fd) 
{
	/* FIXME: mutex around struct data.. */
	int cnt=0;

	sys_sem_wait( fifo->sem ); /* enter critical */

	LWIP_DEBUGF( SIO_FIFO_DEBUG,("fifoput: len%d dat%d empt%d --> ", fifo->len, fifo->dataslot, fifo->emptyslot ) );

	if ( fifo->emptyslot < fifo->dataslot )
	{
		cnt = read( fd, &fifo->data[fifo->emptyslot], fifo->dataslot - fifo->emptyslot );
	} 
	else
	{
		cnt = read( fd, &fifo->data[fifo->emptyslot], FIFOSIZE-fifo->emptyslot );
	}
	fifo->emptyslot += cnt;
	fifo->len += cnt;

	LWIP_DEBUGF( SIO_FIFO_DEBUG,("len%d dat%d empt%d\n", fifo->len, fifo->dataslot, fifo->emptyslot ) );

	if ( fifo->len > FIFOSIZE )
	{
		printf( "ERROR: fifo overrun detected len=%d, flushing\n", fifo->len );
		fifo->dataslot  = 0;
		fifo->emptyslot = 0;
		fifo->len = 0;
	}

	if ( fifo->emptyslot == FIFOSIZE )
	{
		fifo->emptyslot = 0;
		LWIP_DEBUGF( SIO_FIFO_DEBUG, ("(WRAP) ") );

		sys_sem_signal( fifo->sem ); /* leave critical */
		fifoPut( fifo, fd );
		return;
	}
	if ( fifo->getWaiting )
	{
		fifo->getWaiting = FALSE;
		sys_sem_signal( fifo->getSem );
	}

	sys_sem_signal( fifo->sem ); /* leave critical */
	return;
}


void fifoInit(fifo_t * fifo)
{
  fifo->dataslot  = 0;
  fifo->emptyslot = 0;
  fifo->len       = 0;
  fifo->sem    = sys_sem_new(1);  /* critical section 1=free to enter */
  fifo->getSem = sys_sem_new(0);  /* 0 = no one waiting */
  fifo->getWaiting = FALSE;
}
