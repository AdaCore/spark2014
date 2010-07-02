/*****************************************************************************
                              IPSTACK COMPONENTS
               Copyright (C) 2010, Free Software Foundation, Inc.
 ****************************************************************************/

/* C function wrappers to macros or direct access to structure components,
   for Ada binding purposes.  */

#include "lwip/netbuf.h"
#include "lwip/tcp.h"

u16_t
tcp_sndbuf_w (struct tcp_pcb * pcb)
{
  return tcp_sndbuf(pcb);
}

void
tcp_accepted_w (struct tcp_pcb * pcb)
{
  tcp_accepted (pcb);
}

u16_t
netbuf_fromaddr_w (struct netbuf * buf)
{
  return netbuf_fromaddr (buf);
}

u16_t
netbuf_fromport_w (struct netbuf * buf)
{
  return netbuf_fromport (buf);
}

u16_t
pbuf_len_w (struct pbuf * buf)
{
  return buf->len;
}

u16_t
pbuf_tot_len_w (struct pbuf * buf)
{
  return buf->tot_len;
}

void *
pbuf_payload_w (struct pbuf * buf)
{
  return buf->payload;
}

struct pbuf *
pbuf_next_w (struct pbuf * buf)
{
  return buf->next;
}

/* C void wrappers to non-void functions, placing return value in passed mem
   location.  Useful to allow binding by Ada procedures instead of functions,
   hence description of global side effects in SPARK.  */

void pbuf_alloc_w (pbuf_layer l, u16_t size, pbuf_type type,
		   struct pbuf ** retval)
{
  *retval = pbuf_alloc (l, size, type);
}

void pbuf_free_w (struct pbuf * pbuf, u8_t * retval)
{
  *retval = pbuf_free (pbuf);
}

/* Vice-Versa, for callback purposes.  */


extern void
echo_sent_cb (void * sid, void * tcb, u16_t len, err_t * err);

err_t
echo_sent_cb_w (void * sid, void * tcb, u16_t len)
{
  err_t err;
  echo_sent_cb (sid, tcb, len, &err);
  return err;
}

extern void
echo_poll_cb (void * sid, void * tcb, err_t * err);

err_t echo_poll_cb_w (void * sid, void * tcb)
{
  err_t err;
  echo_poll_cb (sid, tcb, &err);
  return err;
}

extern void
echo_recv_cb (void * sid, void * tcb, void * pbu, err_t errin, err_t * err);

err_t
echo_recv_cb_w (void * sid, void * tcb, void * pbu, err_t errin)
{
  err_t err;
  echo_recv_cb (sid, tcb, pbu, errin, &err);
  return err;
}

extern void
echo_accept_cb (void * arg, void * tcb, err_t errin, err_t * err);

err_t
echo_accept_cb_w (void * arg, void * tcb, err_t errin)
{
  err_t err;
  echo_accept_cb (arg, tcb, errin, &err);
  return err;
}
