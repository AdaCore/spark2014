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
* Copyright (C) 2010, AdaCore
*
*********************************************************************************************************
*/

#ifndef _NE2K_H_
#define _NE2K_H_

#include "aip.h"

#define     MIN_PACKET_SIZE 60    /* smallest legal size packet, no fcs    */
#define     MAX_PACKET_SIZE 1514  /* largest legal size packet, no fcs     */

#define	    DELAY		0x590b2  /*0.5s test by ming */
#define	    DELAY_2S		0xbf000  /*2s test */
#define     DELAY_MS		0x38F4   /*20ms test */


/**
 *  Driver functions.
 */
void ne2kif_init (char *Params, Err_T *Err, Netif_Id *Nid);
int ne2kif_isr (Netif_Id Nid);

U16_T write_AX88796(U8_T * buf, U16_T remote_Addr, U16_T Count);

U16_T read_AX88796(U8_T * buf, U16_T remote_Addr, U16_T Count);


/*----------------------------------------
* Register header of NE2000 chip
*----------------------------------------*/
#define Base_ADDR           (0x80000000 + 0x300) /* and ethernet chip is at 0x300 by default */

/* actual address on DSK */
#define     EN_CMD          *(volatile unsigned char *)(Base_ADDR+0x00)  /*	The command register (for all pages) */
#define     EN_DATA	    *(volatile unsigned short *)(Base_ADDR+0x10)	/*by ming (change to 16bit)  Remote DMA Port10~17h (for all pages)*/
#define     EN_RESET	    *(volatile unsigned char *)(Base_ADDR+0x1F)	/*  Reset Port 1fh(for all pages)     */

/* Page 0 register offsets   */
#define     EN0_STARTPG     *(volatile unsigned char *)(Base_ADDR+0x01)	/*  WR Starting page of ring buffer      */
#define     EN0_STOPPG  	*(volatile unsigned char *)(Base_ADDR+0x02)	/*  WR Ending page +1 of ring buffer     */
#define     EN0_BOUNDARY	*(volatile unsigned char *)(Base_ADDR+0x03)	/*  RD/WR Boundary page of ring buffer   */
#define     EN0_TSR		*(unsigned char *)(Base_ADDR+0x04)	/*  RD Transmit status reg               */
#define     EN0_TPSR		*(volatile unsigned char *)(Base_ADDR+0x04)	/*  WR Transmit starting page            */
#define     EN0_NCR		*(volatile unsigned char *)(Base_ADDR+0x05)	/*  RD Number of collision reg           */
#define     EN0_TCNTLO  	*(volatile unsigned char *)(Base_ADDR+0x05)	/*  WR Low  byte of tx byte count        */
#define     EN0_CRP		*(volatile unsigned char *)(Base_ADDR+0x06)	/*  Current Page Register                              */
#define     EN0_TCNTHI		*(volatile unsigned char *)(Base_ADDR+0x06)	/*  WR High byte of tx byte count        */
#define     EN0_ISR		*(volatile unsigned char *)(Base_ADDR+0x07)	/*  RD/WR Interrupt status reg           */
#define     EN0_CRDALO  	*(volatile unsigned char *)(Base_ADDR+0x08)	/*  RD low byte of current remote dma add*/
#define     EN0_RSARLO		*(volatile unsigned char *)(Base_ADDR+0x08)	/*  WR Remote start address reg 0        */
#define     EN0_CRDAHI		*(volatile unsigned char *)(Base_ADDR+0x09)	/*  RD high byte, current remote dma add.*/
#define     EN0_RSARHI		*(volatile unsigned char *)(Base_ADDR+0x09)	/*  WR Remote start address reg 1        */
#define     EN0_RCNTLO	    	*(volatile unsigned char *)(Base_ADDR+0x0A)	/*  WR Remote byte count reg 0           */
#define     EN0_RCNTHI		*(volatile unsigned char *)(Base_ADDR+0x0B)	/*  WR Remote byte count reg 1           */
#define     EN0_RSR		*(volatile unsigned char *)(Base_ADDR+0x0C)	/*  RD RX status reg                     */
#define     EN0_RXCR		*(volatile unsigned char *)(Base_ADDR+0x0C)	/*  WR RX configuration reg              */
#define     EN0_TXCR		*(volatile unsigned char *)(Base_ADDR+0x0D)	/*  WR TX configuration reg              */
#define     EN0_DCFG		*(volatile unsigned char *)(Base_ADDR+0x0E)	/*  WR Data configuration reg            */
#define     EN0_IMR		*(volatile unsigned char *)(Base_ADDR+0x0F)	/*  WR Interrupt mask reg                */

/* Page 1 register offsets    */
#define     EN1_PAR0	    *(volatile unsigned char *)(Base_ADDR+0x01)	/* RD/WR This board's physical ethernet addr */
#define     EN1_PAR1	    *(volatile unsigned char *)(Base_ADDR+0x02)
#define     EN1_PAR2	    *(volatile unsigned char *)(Base_ADDR+0x03)
#define     EN1_PAR3	    *(volatile unsigned char *)(Base_ADDR+0x04)
#define     EN1_PAR4	    *(volatile unsigned char *)(Base_ADDR+0x05)
#define     EN1_PAR5	    *(volatile unsigned char *)(Base_ADDR+0x06)
#define     EN1_CURR	    *(volatile unsigned char *)(Base_ADDR+0x07)   /* RD/WR current page reg */
#define		EN1_CURPAG		EN1_CURR
#define     EN1_MAR0        *(volatile unsigned char *)(Base_ADDR+0x08)   /* RD/WR Multicast filter mask array (8 bytes) */
#define     EN1_MAR1	    *(volatile unsigned char *)(Base_ADDR+0x09)
#define     EN1_MAR2        *(volatile unsigned char *)(Base_ADDR+0x0A)
#define     EN1_MAR3        *(volatile unsigned char *)(Base_ADDR+0x0B)
#define     EN1_MAR4        *(volatile unsigned char *)(Base_ADDR+0x0C)
#define     EN1_MAR5        *(volatile unsigned char *)(Base_ADDR+0x0D)
#define     EN1_MAR6        *(volatile unsigned char *)(Base_ADDR+0x0E)
#define     EN1_MAR7        *(volatile unsigned char *)(Base_ADDR+0x0F)

/* Command Values at EN_CMD */
#define     EN_STOP	    0x01	/*  Stop and reset the chip */
#define     EN_START	    0x02	/*  Start the chip, clear reset */
#define     EN_TRANS	    0x04	/*  Transmit a frame */
#define     EN_RREAD	    0x08	/*  Remote read */
#define     EN_RWRITE	    0x10	/*  Remote write */
#define     EN_NODMA	    0x20	/*  Remote DMA */
#define     EN_PAGE0	    0x00	/*  Select page chip registers */
#define     EN_PAGE1	    0x40	/*  using the two high-order bits */


/*---------------------------------
  Values for Ring-Buffer setting
  --------------------------------- */

#define     NE_START_PG	    0x40     	/* First page of TX buffer */
#define     NE_STOP_PG	    0x80	/* Last page + 1 of RX Ring */

#define     TX_PAGES	    6
#define	    TX_START_PG	    NE_START_PG	/*0x40*/

#define     RX_START_PG	    (NE_START_PG + TX_PAGES) /*0x46*/
#define     RX_CURR_PG      (RX_START_PG + 1)		   /*0x47*/
#define     RX_STOP_PG      NE_STOP_PG  /*0x80*/


/* Bits in EN0_ISR - Interrupt status register        (RD WR)                */
#define     ENISR_RX   	    0x01	/*  Receiver, no error */
#define     ENISR_TX	    0x02	/*  Transceiver, no error */
#define     ENISR_RX_ERR    0x04	/*  Receiver, with error */
#define     ENISR_TX_ERR    0x08	/*  Transmitter, with error */
#define     ENISR_OVER	    0x10	/*  Receiver overwrote the ring */
                       			/*  Gap area of receiver ring buffer was disappeared  */

#define     ENISR_COUNTERS	0x20	/*  Counters need emptying */
                                    /*  MSB of network tally counter became 1 */
#define     ENISR_RDC	    0x40	/*  remote dma complete */
#define     ENISR_RESET     0x80	/*  Reset completed */
#define     ENISR_ALL	    0x3f	/*  3f  Interrupts we will enable */
                                	/*  RST RDC CNT OVW TXE RXE PTX PRX */


/* Bits in EN0_RXCR - RX configuration reg                                   */
/*#define     ENRXCR_RXCONFIG 0x04 	*//* EN0_RXCR: broadcasts,no multicast,errors */
#define     ENRXCR_RXCONFIG 0x00 	/* EN0_RXCR: only unicast */
#define     ENRXCR_CRC	    0x01	/*  Save error packets(admit) */
#define     ENRXCR_RUNT	    0x02	/*  Accept runt pckt(below 64bytes) */
#define     ENRXCR_BCST	    0x04	/*  Accept broadcasts when 1 */
#define     ENRXCR_MULTI    0x08	/*  Multicast (if pass filter) when 0*/
#define     ENRXCR_PROMP    0x10	/*  Promiscuous physical addresses when 1*/
					/* when 0,accept assigned PAR0~5 address */
#define     ENRXCR_MON	    0x20	/*  Monitor mode (no packets rcvd) */

/* Bits in EN0_TXCR - TX configuration reg                                   */
#define     ENTXCR_TXCONFIG 0x00    /* Normal transmit mode                  */
#define     ENTXCR_CRC	    0x01    /*  inhibit CRC,do not append crc when 1 */
#define     ENTXCR_LOOP	    0x02    /*  set internal loopback mode     ?     */
#define     ENTXCR_LB01	    0x06    /*  encoded loopback control       ?     */
#define     ENTXCR_ATD	    0x08    /*  auto tx disable                      */
/* when 1, if specified multicast packet was received, disable transmit      */
#define     ENTXCR_OFST	    0x10	/*  collision offset enable */
/* selection of collision algorithm. When 0, gererally back-off algorithm select */

#endif /* _NE2K_H_ */
