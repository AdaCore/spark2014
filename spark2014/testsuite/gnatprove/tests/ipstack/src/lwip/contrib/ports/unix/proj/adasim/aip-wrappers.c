
/* C function wrappers to macros or direct access to structure
   components, for Ada binding purposes.  */

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
  return buf->len;
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
