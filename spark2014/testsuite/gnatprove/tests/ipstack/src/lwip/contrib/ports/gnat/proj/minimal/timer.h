#ifndef _TIMER_H_
#define _TIMER_H_

#define TIMER_EVT_ETHARPTMR 0
#define TIMER_EVT_TCPFASTTMR 1
#define TIMER_EVT_TCPSLOWTMR 2
#define TIMER_EVT_IPREASSTMR 3
#define TIMER_NUM 4

void timer_init(void);
void timer_set_interval(unsigned char tmr, unsigned int interval);
unsigned char timer_testclr_evt(unsigned char tmr);

#endif
