/*
*********************************************************************************************************
*                                              lwIP TCP/IP Stack
*                                    	 port for uC/OS-II RTOS on TIC6711 DSK
*
* File : tcp_ip.c
* By   : ZengMing @ DEP,Tsinghua University,Beijing,China
* Reference: YangYe's source code for SkyEye project
*
* Port for AIP
* Copyright (C) 2010-2012, AdaCore
*
*********************************************************************************************************
*/

#include "ne2kif.h"

/* Define those to better describe your network interface. */
#define IFNAME0 'n'
#define IFNAME1 'e'

struct ne2k_if {
  Ethernet_Address *ethaddr; /*MAC Address */
};

static struct ne2k_if ne2k_if;
struct netif *ne2k_if_netif;    /* Assumes single NE2k interface??? */

static void low_level_init(struct netif * netif);
static void arp_timer(void *arg);
static void low_level_output(Netif_Id Nid, Buffer_Id p, Err_T *Err);
static void ne2k_configured (Netif_Id Nid, Err_T *Err);
static void ne2k_input (Netif_Id Nid);
static Buffer_Id low_level_input(struct netif *netif);

/*----------------------------------------------------------------------------------------
  ****************************************************************************************
  ----------------------------------------------------------------------------------------*/

/*
 * ethernetif_init():
 *
 * Should be called at the beginning of the program to set up the
 * network interface. It calls the function low_level_init() to do the
 * actual setup of the hardware.
 *
 */
static int initialized = 0;
void ne2kif_init (char *Params, Err_T *Err, Netif_Id *Nid)
{
  struct netif *netif;

   if (initialized) {
    *Err = ERR_MEM;
    return;
  }

  AIP_allocate_netif (Nid);
  if (*Nid == IF_NOID) {
    *Err = ERR_MEM;
    return;
  }

  netif = AIP_get_netif (*Nid);

 /*
  struct ne2k_if *ne2k_if;

  printf ("Initializing ne2k if %c%c...", IFNAME0, IFNAME1);

  ne2k_if = mem_malloc(sizeof(struct ne2k_if));

  if (ne2k_if == NULL)
    return ERR_MEM;
  */

  netif->Dev = &ne2k_if;
  netif->Name[0] = IFNAME0;
  netif->Name[1] = IFNAME1;

  netif->Offload[IP_CS]   = 0;
  netif->Offload[ICMP_CS] = 0;
  netif->Offload[UDP_CS]  = 0;
  netif->Offload[TCP_CS]  = 0;

  netif->Configured_CB  = ne2k_configured;
  netif->Input_CB       = AIP_ip_input;
  netif->Output_CB      = AIP_arp_output;
  netif->Link_Output_CB = low_level_output;

  ne2k_if.ethaddr = (Ethernet_Address *)&(netif->LL_Address[0]);

  low_level_init(netif);
  *Err = NOERR;
}

/**
 * Initialize the ne2k ethernet chip, resetting the interface and getting the ethernet
 * address.
 */
static void low_level_init(struct netif * netif)
{
  U16_T i;
  struct ne2k_if *ne2k_if;

  ne2k_if = netif->Dev;
  /* the meaning of "netif->state" can be defined in drivers,
     here for MAC address! */

  netif->LL_Address_Length = 6;
  netif->MTU = 1500;
/* netif->flags = NETIF_FLAG_BROADCAST; ??? */

  /* ---------- start ------------- */

  i = EN_RESET; /*this instruction let NE2K chip soft reset*/

  for (i=0;i<DELAY_MS;i++)
    ; /*wait*/

  EN_CMD = (U8_T) (EN_PAGE0 + EN_NODMA + EN_STOP);

  EN0_DCFG = (U8_T) 0x01;

  /* Clear the remote	byte count registers. */
  EN0_RCNTHI = (U8_T) 0x00;  /* MSB remote byte count reg */
  EN0_RCNTLO = (U8_T) 0x00;  /* LSB remote byte count reg */

  /* RX configuration reg    Monitor mode (no packet receive) */
  EN0_RXCR = (U8_T) ENRXCR_MON;
  /* TX configuration reg   set internal loopback mode  */
  EN0_TXCR = (U8_T) ENTXCR_LOOP;

  EN0_TPSR = (U8_T) 0x40;

  EN0_STARTPG = (U8_T) 0x46 ; /* Starting page of ring buffer. First page of Rx ring buffer 46h*/
  EN0_BOUNDARY = (U8_T) 0x46 ;  /* Boundary page of ring buffer 0x46*/
  EN0_STOPPG = (U8_T) 0x80 ;   /* Ending page of ring buffer ,0x80*/

  EN0_ISR = (U8_T) 0xff; /* clear the all flag bits in EN0_ISR */
  EN0_IMR = (U8_T) 0x00; /* Disable all Interrupt */

  /* Read ethernet address.  */
  EN_CMD = (U8_T) (EN_PAGE0 + EN_RREAD + EN_STOP);
  EN0_RSARLO = 0;
  EN0_RSARHI = 0;
  EN0_RCNTLO = 6;
  EN0_RCNTHI = 0;

  for (i = 0; i < 6; i++)
    (*ne2k_if->ethaddr)[i] = EN_DATA;

  EN_CMD = (U8_T) (EN_PAGE1 + EN_NODMA + EN_STOP);
  EN1_CURR = (U8_T) 0x47; /* keep curr=boundary+1 means no new packet */

  EN1_PAR0 = (*ne2k_if->ethaddr)[0];
  EN1_PAR1 = (*ne2k_if->ethaddr)[1];
  EN1_PAR2 = (*ne2k_if->ethaddr)[2];
  EN1_PAR3 = (*ne2k_if->ethaddr)[3];
  EN1_PAR4 = (*ne2k_if->ethaddr)[4];
  EN1_PAR5 = (*ne2k_if->ethaddr)[5];

  /*
  printf ("MAC addr:");
  for (i = 0; i < 6; i++)
    printf ("%c%02x", i == 0 ? ' ' : ':', (*ne2k_if->ethaddr)[i]);
  */

  /* Initialize the multicast list to reject-all.
     If we enable multicast the higher levels can do the filtering.
     <multicast filter mask array (8 bytes)> */
  EN1_MAR0 = (U8_T) 0x00;
  EN1_MAR1 = (U8_T) 0x00;
  EN1_MAR2 = (U8_T) 0x00;
  EN1_MAR3 = (U8_T) 0x00;
  EN1_MAR4 = (U8_T) 0x00;
  EN1_MAR5 = (U8_T) 0x00;
  EN1_MAR6 = (U8_T) 0x00;
  EN1_MAR7 = (U8_T) 0x00;

  EN_CMD = (U8_T) (EN_PAGE0 + EN_NODMA + EN_STOP);

  EN0_IMR = (U8_T) (ENISR_OVER + ENISR_RX + ENISR_RX_ERR);

  EN0_TXCR = (U8_T) 0x00; /*E0			//TCR*/
  EN0_RXCR = (U8_T) 0x44;	/*CC			//RCR*/

  EN_CMD = (U8_T) (EN_PAGE0 + EN_NODMA + EN_START);

  EN0_ISR = (U8_T) 0xff; /* clear the all flag bits in EN0_ISR*/

  ne2k_if_netif = netif;
}


/*----------------------------------------------------------------------------------------
  ****************************************************************************************
  ----------------------------------------------------------------------------------------*/

/*
 * low_level_output():
 *
 * Should do the actual transmission of the packet. The packet is
 * contained in the pbuf that is passed to the function. This pbuf
 * might be chained.
 *
 */
static void low_level_output(Netif_Id Nid, Buffer_Id p, Err_T *Err)
{
  struct netif *netif = AIP_get_netif (Nid);
  Buffer_Id q;
  U16_T packetLength,remote_Addr,Count,Written;
  U8_T *buf;

  packetLength = AIP_buffer_tlen (p);

  if ((packetLength) < 64)
    packetLength = 64; /*add pad by the AX88796 automatically*/

  /* turn off RX int	*/
  EN0_IMR = (U8_T) (ENISR_OVER);

  /* We should already be in page 0, but to be safe... */
  EN_CMD = (U8_T) (EN_PAGE0 + EN_START + EN_NODMA);

  /* clear the RDC bit	*/
  EN0_ISR = (U8_T) ENISR_RDC;

  remote_Addr = (U16_T)(TX_START_PG<<8);

  /*
   * Write packet to ring buffers.
   */
  Written = 0;
  for(q = p; Written < AIP_buffer_tlen (p); q = AIP_buffer_next (q)) {
    /* Send the data from the pbuf to the interface, one pbuf at a
       time. */
    Count = AIP_buffer_len (q);
    buf = AIP_buffer_payload (q);

    /* Write data to AX88796*/
    remote_Addr = write_AX88796(buf, remote_Addr, Count);
    Written += Count;
  }

  /* Just send it, and does not check */
  while (EN_CMD & EN_TRANS)
    ;

  EN0_TPSR   = (U8_T)  TX_START_PG;
  EN0_TCNTLO = (U8_T) (packetLength & 0xff);
  EN0_TCNTHI = (U8_T) (packetLength >> 8);
  EN_CMD = (U8_T) (EN_PAGE0 + EN_NODMA + EN_TRANS + EN_START);

  EN0_IMR = (U8_T) (ENISR_OVER + ENISR_RX + ENISR_RX_ERR);

#if LINK_STATS
  lwip_stats.link.xmit++;
#endif /* LINK_STATS */

  *Err = NOERR;
}

/**
 *  write_AX88796.
 */
U16_T write_AX88796(U8_T * buf, U16_T remote_Addr, U16_T Count)
{
  U16_T loop;

  /* AX88796. */
  EN0_RCNTLO = (U8_T) ( Count &  0xff);
  EN0_RCNTHI = (U8_T) ( Count >> 8);
  EN0_RSARLO = (U8_T) ( remote_Addr &  0xff);
  EN0_RSARHI = (U8_T) ( remote_Addr >> 8);
  EN_CMD     = (U8_T) (EN_RWRITE + EN_START + EN_PAGE0);

  /* Add for next loop...*/
  remote_Addr += Count;

  Count = (Count + 1) >> 1; /* Turn to 16bits count. <Must add 1 first!> */

  for (loop=0;loop < Count ;loop++){
    EN_DATA = *(U16_T *)buf;
    buf += 2;
  }

  while ((EN0_ISR & ENISR_RDC) == 0)
    ;

  EN0_ISR = (U8_T) ENISR_RDC;

  return remote_Addr;
}


/*--------------------------------------------------------------------------
  **************************************************************************
  --------------------------------------------------------------------------*/

static void
ne2k_configured (Netif_Id Nid, Err_T *Err) {
  *Err = NOERR;
}

/*
 * ethernetif_input():
 *
 * This function should be called when a packet is ready to be read
 * from the interface. It uses the function low_level_input() that
 * should handle the actual reception of bytes from the network
 * interface.
 *
 */
static void
ne2k_input (Netif_Id Nid)
{
  struct netif *netif = AIP_get_netif (Nid);
  struct ne2k_if *ne2k_if;
  void *ethhdr;
  Buffer_Id p;
  Err_T Err;

  ne2k_if = netif->Dev;

  /* move received packet into a new pbuf */
  p = low_level_input(netif);
  /* no packet could be read, silently ignore this */
  if (p == NOBUF) return;
  /* points to packet payload, which starts with an Ethernet header */
  ethhdr = AIP_buffer_payload (p);

#if LINK_STATS
  lwip_stats.link.recv++;
#endif /* LINK_STATS */

  switch (AIP_EtherH_Frame_Type (ethhdr)) {
    /* IP packet? */
  case Ether_Type_IP:
      /* update ARP table */

      AIP_arpip_input (Nid, p);

      /* skip Ethernet header */

      AIP_buffer_header(p, -14, &Err);

      if (Err == NOERR) {
	/* pass to network layer */
	netif->Input_CB (Nid, p);
      } else {
	AIP_buffer_blind_free (p);
      }
      break;

  case Ether_Type_ARP:
      /* pass p to ARP module */

      AIP_arp_input(Nid, ne2k_if->ethaddr, p);
      break;

  default:
    AIP_buffer_blind_free (p);
    p = NOBUF;
    break;
  }
}

/*
 * low_level_input():
 *
 * Should allocate a pbuf and transfer the bytes of the incoming
 * packet from the interface into the pbuf.
 *
 */
static Buffer_Id
low_level_input(struct netif *netif)
{
  U16_T packetLength, Count, remote_Addr;
  U8_T  *buf, PDHeader[4];
  U8_T  curr, this_frame, next_frame;
  Buffer_Id p, q, r;

  EN_CMD     = (U8_T) (EN_PAGE1 + EN_NODMA + EN_START);
  curr       = (U8_T)  EN1_CURR;
  EN_CMD     = (U8_T) (EN_PAGE0 + EN_NODMA + EN_START);
  this_frame = (U8_T)  EN0_BOUNDARY + 1;

  if (this_frame >= RX_STOP_PG)
    this_frame = RX_START_PG;

  /*---------- get the first 4 bytes from AX88796 ---------*/
  (void) read_AX88796(PDHeader, (U16_T)(this_frame<<8), 4);


  /*----- Store real length, set len to packet length - header ---------*/
  packetLength = ((unsigned) PDHeader[2] | (PDHeader[3] << 8 )) - 4; /* minus PDHeader[4]*/
  next_frame = (U8_T) (this_frame + 1 + ((packetLength + 4) >> 8));

  /* Bad frame!*/
  if ((PDHeader[1] != (U8_T)next_frame) && (PDHeader[1] != (U8_T)(next_frame + 1))
      && (PDHeader[1] != (U8_T)(next_frame - RX_STOP_PG + RX_START_PG))
      && (PDHeader[1] != (U8_T)(next_frame + 1 - RX_STOP_PG + RX_START_PG)))
    {
      EN0_BOUNDARY = (U8_T) (curr - 1);
      return NOBUF;
    }

  /* Bogus Packet Size*/
  if (packetLength > MAX_PACKET_SIZE || packetLength < MIN_PACKET_SIZE)
    {
      next_frame = PDHeader[1];
      EN0_BOUNDARY = (U8_T) (next_frame-1);
      return NOBUF;
    }


  EN_CMD = (U8_T) (EN_PAGE0 + EN_NODMA + EN_START);

  EN0_ISR = (U8_T) ENISR_RDC;	/* clear the RDC bit	*/

  remote_Addr = (U16_T)((this_frame << 8) + 4);

  if ((remote_Addr + packetLength) > (U16_T)(RX_STOP_PG<<8)) {
    AIP_buffer_alloc (0, (U16_T)(RX_STOP_PG<<8) - remote_Addr, LINK_BUF, &p);
    packetLength -= (U16_T)(RX_STOP_PG<<8) - remote_Addr;
  } else {
    AIP_buffer_alloc (0, packetLength, LINK_BUF, &p);
    packetLength = 0;
  }

  if(p != NOBUF) { /* We iterate over the pbuf chain until we have read the entire packet into the pbuf. */
    for(q = p; q != NOBUF; q = AIP_buffer_next (q)){ /* Read enough bytes to fill this pbuf in the chain. The avaliable data in the pbuf is given by the q->len variable. */
      buf = AIP_buffer_payload (q);
      Count = AIP_buffer_len (q);
      remote_Addr = read_AX88796(buf, remote_Addr, Count);

#if LINK_STATS
      lwip_stats.link.recv++;
#endif /* LINK_STATS */
    }
  }
  else
    {
#if LINK_STATS
      lwip_stats.link.memerr++;
      lwip_stats.link.drop++;
#endif /* LINK_STATS */
    }


  if (packetLength) /* ring buffer cycled */
    {
      remote_Addr = (U16_T)(RX_START_PG << 8);
      AIP_buffer_alloc (0, packetLength, LINK_BUF, &r);

      if(r != NOBUF) { /* We iterate over the pbuf chain until we have read the entire packet into the pbuf. */
        for(q = r; q != NOBUF; q = AIP_buffer_next (q)){ /* Read enough bytes to fill this pbuf in the chain. The avaliable data in the pbuf is given by the q->len variable. */
          buf = AIP_buffer_payload (q);
          Count = AIP_buffer_len (q);
          remote_Addr = read_AX88796(buf, remote_Addr, Count);
        }
        /* link pbuf p & r */
        AIP_buffer_cat (p, r);
      }
      else
        {
#if LINK_STATS
          lwip_stats.link.memerr++;
          lwip_stats.link.drop++;
#endif
        }
    }

  next_frame = PDHeader[1];

  EN0_BOUNDARY = (U8_T) (next_frame-1);

  return p;
}

/**
 *  read_AX88796.
 */
U16_T read_AX88796(U8_T * buf, U16_T remote_Addr, U16_T Count)
{
  U8_T  flagOdd=0;
  U16_T loop;

  flagOdd = (Count & 0x0001); /* set Flag if Count is odd.*/

  Count -= flagOdd;

  EN0_RCNTLO = (U8_T) (Count & 0xff);
  EN0_RCNTHI = (U8_T) (Count >> 8);
  EN0_RSARLO = (U8_T) (remote_Addr & 0xff);
  EN0_RSARHI = (U8_T) (remote_Addr >> 8);
  EN_CMD = (U8_T) (EN_PAGE0 + EN_RREAD + EN_START);

  remote_Addr += Count;

  Count = Count>>1;

  for (loop=0;loop < Count ;loop++){
    *(U16_T *)buf = EN_DATA ;
    buf += 2;
  }

  while ((EN0_ISR & ENISR_RDC) == 0)
    ;

  EN0_ISR = (U8_T) ENISR_RDC;

  if (flagOdd) {
    EN0_RCNTLO = 0x01;
    EN0_RCNTHI = 0x00;
    EN0_RSARLO = (U8_T) (remote_Addr & 0xff);
    EN0_RSARHI = (U8_T) (remote_Addr >> 8);
    EN_CMD = (U8_T) (EN_PAGE0 + EN_RREAD + EN_START);

    remote_Addr += 1;

    *(U8_T *)buf = *(U8_T *)(Base_ADDR+0x10) ;

    while ((EN0_ISR & ENISR_RDC) == 0);

    EN0_ISR = (U8_T) ENISR_RDC;
  }

  return remote_Addr;
}

/*--------------------------------------------------------------------------
  **************************************************************************
  --------------------------------------------------------------------------*/

/**
 *  ne2k_rx_err.
 */
void ne2k_rx_err(void)
{
  U8_T  curr;
  EN_CMD = (U8_T) (EN_PAGE1 + EN_NODMA + EN_STOP);
  curr = (U8_T) EN1_CURR;
  EN_CMD = (U8_T) (EN_PAGE0 + EN_NODMA + EN_STOP);
  EN0_BOUNDARY = (U8_T) curr-1;
}

/**
 *  ne2k_rx.
 */
void ne2k_rx(Netif_Id Nid)
{
  U8_T  curr,bnry,loopCnt = 0;

  while(loopCnt < 10) {

    EN_CMD = (U8_T) (EN_PAGE1 + EN_NODMA + EN_STOP);
    curr = (U8_T) EN1_CURR;
    EN_CMD = (U8_T) (EN_PAGE0 + EN_NODMA + EN_STOP);
    bnry = (U8_T) EN0_BOUNDARY + 1;

    if (bnry >= RX_STOP_PG)
      bnry = RX_START_PG;

    if (curr == bnry) break;

    ne2k_input (Nid);

    loopCnt++;
  }
}

/*---*---*---*---*---*---*---*
 *     void ne2kif_isr(void)
 *    can be int 4 5 6 or 7
 *---*---*---*---*---*---*---*/
int ne2kif_isr(Netif_Id Nid)
{
  if (EN0_ISR == 0)
    return 0;

  EN_CMD = (U8_T) (EN_PAGE0 + EN_NODMA + EN_STOP);
  /*outb(CMD_PAGE0 | CMD_NODMA | CMD_STOP,NE_CR);*/

  EN0_IMR = (U8_T) 0x00;/*close*/

  /* ram overflow interrupt*/
  if (EN0_ISR & ENISR_OVER) {
    EN0_ISR = (U8_T) ENISR_OVER;		/* clear interrupt*/
  }

  /* error transfer interrupt ,NIC abort tx due to excessive collisions	*/
  if (EN0_ISR & ENISR_TX_ERR) {
    EN0_ISR = (U8_T) ENISR_TX_ERR;		/* clear interrupt*/
    /*temporarily do nothing*/
  }

  /* Rx error , reset BNRY pointer to CURR (use SEND PACKET mode)*/
  if (EN0_ISR & ENISR_RX_ERR) {
    EN0_ISR = (U8_T) ENISR_RX_ERR;		/* clear interrupt*/
    ne2k_rx_err();
  }

  /*got packet with no errors*/
  if (EN0_ISR & ENISR_RX) {
    EN0_ISR = (U8_T) ENISR_RX;
    ne2k_rx (Nid);
  }

  /*Transfer complelte, do nothing here*/
  if (EN0_ISR & ENISR_TX){
    EN0_ISR = (U8_T) ENISR_TX;		/* clear interrupt*/
  }

  EN_CMD = (U8_T) (EN_PAGE0 + EN_NODMA + EN_STOP);

  EN0_ISR = (U8_T) 0xff;			/* clear ISR	*/

  EN0_IMR = (U8_T) (ENISR_OVER + ENISR_RX + ENISR_RX_ERR);

  /*open nic for next packet*/
  EN_CMD = (U8_T) (EN_PAGE0 + EN_NODMA + EN_START);

  return 1;
}
