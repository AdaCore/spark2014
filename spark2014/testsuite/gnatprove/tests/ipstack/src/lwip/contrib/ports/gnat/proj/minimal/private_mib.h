/**
 * @file
 * Exports Private lwIP MIB 
 */

#ifndef __LWIP_PRIVATE_MIB_H__
#define __LWIP_PRIVATE_MIB_H__

#include "arch/cc.h"
#include "lwip/opt.h"

#if LWIP_SNMP
#include "lwip/snmp_structs.h"
extern const struct mib_array_node private;

/** @todo remove this?? */
struct private_msg
{
  u8_t dummy;
};

void lwip_privmib_init(void);

#endif

#endif
