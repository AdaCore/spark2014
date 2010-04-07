/**
 * @file
 * lwip Private MIB 
 *
 * @todo create MIB file for this example
 * @note the lwip enterprise tree root (26381) is owned by the lwIP project.
 * It is NOT allowed to allocate new objects under this ID (26381) without our,
 * the lwip developers, permission!
 *
 * Please apply for your own ID with IANA: http://www.iana.org/numbers.html
 *  
 * lwip        OBJECT IDENTIFIER ::= { enterprises 26381 }
 * example     OBJECT IDENTIFIER ::= { lwip 1 }
 */
 
/*
 * Copyright (c) 2006 Axon Digital Design B.V., The Netherlands.
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
 * Author: Christiaan Simons <christiaan.simons@axon.tv>
 */

#include <sys/stat.h>
#include <sys/types.h>
#include <ctype.h>
#include <unistd.h>
#include <fcntl.h>
#include <dirent.h>

#include "private_mib.h"
#include "lwip/snmp_msg.h"
#include "lwip/snmp_asn1.h"

/*
  This example presents a table for a few (at most 10) sensors.
  Sensor detection takes place at initialization (once only).
  Sensors may and can not be added or removed after agent
  has started. Note this is only a limitation of this crude example,
  the agent does support dynamic object insertions and removals.
   
  You'll need to manually create a directory called "sensors" and
  a few single line text files with an integer temperature value.
  The files must be called [0..9].txt. 
   
  ./sensors/0.txt [content: 20]
  ./sensors/3.txt [content: 75]
    
  The sensor values may be changed in runtime by editing the 
  text files in the "sensors" directory.
*/
   
#define SENSOR_MAX 10
#define SENSOR_NAME_LEN 20
#define SENSORS_DIR "sensors"
struct sensor_inf
{
  char sensor_files[SENSOR_MAX][SENSOR_NAME_LEN + 1];
  /* (Sparse) list of sensors (table index),
   the actual "hot insertion" is done in lwip_privmib_init() */
  struct mib_list_rootnode sensor_list_rn;
};

struct sensor_inf sensor_addr_inf =
{
  {{0}},
  {
    NULL,
    NULL,
    NULL,
    NULL,
    MIB_NODE_LR,
    0,
    NULL,
    NULL,
    0
  }
};


static u16_t sensorentry_length(void* addr_inf, u8_t level);
static s32_t sensorentry_idcmp(void* addr_inf, u8_t level, u16_t idx, s32_t sub_id);
static void sensorentry_get_subid(void* addr_inf, u8_t level, u16_t idx, s32_t *sub_id);

static void sensorentry_get_object_def_q(void* addr_inf, u8_t rid, u8_t ident_len, s32_t *ident);
static void sensorentry_get_object_def_a(u8_t rid, u8_t ident_len, s32_t *ident, struct obj_def *od);
static void sensorentry_get_object_def_pc(u8_t rid, u8_t ident_len, s32_t *ident);
static void sensorentry_get_value_q(u8_t rid, struct obj_def *od);
static void sensorentry_get_value_a(u8_t rid, struct obj_def *od, u16_t len, void *value);
static void sensorentry_get_value_pc(u8_t rid, struct obj_def *od);
static void sensorentry_set_test_q(u8_t rid, struct obj_def *od);
static u8_t sensorentry_set_test_a(u8_t rid, struct obj_def *od, u16_t len, void *value);
static void sensorentry_set_test_pc(u8_t rid, struct obj_def *od);
static void sensorentry_set_value_q(u8_t rid, struct obj_def *od, u16_t len, void *value);
static void sensorentry_set_value_a(u8_t rid, struct obj_def *od, u16_t len, void *value);
static void sensorentry_set_value_pc(u8_t rid, struct obj_def *od);

/* sensorentry .1.3.6.1.4.1.26381.1.1.1 (.level0.level1)
   where level 0 is the object identifier (temperature) and level 1 the index */
struct mib_external_node sensorentry = {
  &noleafs_get_object_def,
  &noleafs_get_value,
  &noleafs_set_test,
  &noleafs_set_value,
  MIB_NODE_EX,
  0,
  &sensor_addr_inf,
  /* 0 tree_levels (empty table) at power-up,
     2 when one or more sensors are detected */
  0,
  &sensorentry_length,
  &sensorentry_idcmp,
  &sensorentry_get_subid,
  
  &sensorentry_get_object_def_q,
  &sensorentry_get_value_q,
  &sensorentry_set_test_q,
  &sensorentry_set_value_q,

  &sensorentry_get_object_def_a,
  &sensorentry_get_value_a,
  &sensorentry_set_test_a,
  &sensorentry_set_value_a,

  &sensorentry_get_object_def_pc,
  &sensorentry_get_value_pc,
  &sensorentry_set_test_pc,
  &sensorentry_set_value_pc
};

/* sensortable .1.3.6.1.4.1.26381.1.1 */
const s32_t sensortable_ids[1] = { 1 };
struct mib_node* const sensortable_nodes[1] = {
 (struct mib_node* const)&sensorentry
};
const struct mib_array_node sensortable = {
  &noleafs_get_object_def,
  &noleafs_get_value,
  &noleafs_set_test,
  &noleafs_set_value,
  MIB_NODE_AR,
  1,
  sensortable_ids,
  sensortable_nodes
};

/* example .1.3.6.1.4.1.26381.1 */
const s32_t example_ids[1] = { 1 };
struct mib_node* const example_nodes[1] = {
  (struct mib_node* const)&sensortable
};
const struct mib_array_node example = {
  &noleafs_get_object_def,
  &noleafs_get_value,
  &noleafs_set_test,
  &noleafs_set_value,
  MIB_NODE_AR,
  1,
  example_ids,
  example_nodes
};

/* lwip .1.3.6.1.4.1.26381 */
const s32_t lwip_ids[1] = { 1 };
struct mib_node* const lwip_nodes[1] = { (struct mib_node* const)&example };
const struct mib_array_node lwip = {
  &noleafs_get_object_def,
  &noleafs_get_value,
  &noleafs_set_test,
  &noleafs_set_value,
  MIB_NODE_AR,
  1,
  lwip_ids,
  lwip_nodes
};

/* enterprises .1.3.6.1.4.1 */
const s32_t enterprises_ids[1] = { 26381 };
struct mib_node* const enterprises_nodes[1] = { (struct mib_node* const)&lwip };
const struct mib_array_node enterprises = {
  &noleafs_get_object_def,
  &noleafs_get_value,
  &noleafs_set_test,
  &noleafs_set_value,
  MIB_NODE_AR,
  1,
  enterprises_ids,
  enterprises_nodes
};

/* private .1.3.6.1.4 */
const s32_t private_ids[1] = { 1 };
struct mib_node* const private_nodes[1] = { (struct mib_node* const)&enterprises };
const struct mib_array_node private = {
  &noleafs_get_object_def,
  &noleafs_get_value,
  &noleafs_set_test,
  &noleafs_set_value,
  MIB_NODE_AR,
  1,
  private_ids,
  private_nodes
};

/**
 * Initialises this private MIB before use.
 * @see main.c
 */
void
lwip_privmib_init(void)
{
  char *buf, *ebuf, *cp;
  size_t bufsize;
  int nbytes;
  struct stat sb;
  struct dirent *dp;
  int fd;
  
  printf("SNMP private MIB start, detecting sensors.\n");
  /* look for sensors in sensors directory */
  fd = open(SENSORS_DIR, O_RDONLY);
  if (fd > -1)
  {
    fstat(fd, &sb);
    bufsize = sb.st_size;
    if (bufsize < sb.st_blksize)
    {
      bufsize = sb.st_blksize;
    }
    buf = malloc(bufsize);
    if (buf != NULL)
    {
      do
      {
        long base;
        
        nbytes = getdirentries(fd, buf, bufsize, &base);
        if (nbytes > 0)
        {
          ebuf = buf + nbytes;
          cp = buf;
          while (cp < ebuf)
          {
            dp = (struct dirent *)cp;
            if (isdigit(dp->d_name[0]))
            {
              struct mib_list_node *dummy;
              unsigned char index;
              
              index = dp->d_name[0] - '0';
              snmp_mib_node_insert(&sensor_addr_inf.sensor_list_rn,index,&dummy);              

              strncpy(&sensor_addr_inf.sensor_files[index][0],dp->d_name,SENSOR_NAME_LEN);              
              printf("%s\n", sensor_addr_inf.sensor_files[index]);
            }
            cp += dp->d_reclen;
          }
        } 
      }
      while (nbytes > 0);
    
      free(buf);
    }
    close(fd);
  }
  if (sensor_addr_inf.sensor_list_rn.count != 0)
  {
    /* enable sensor table, 2 tree_levels under this node
       one for the registers and one for the index */
    sensorentry.tree_levels = 2;
  }
}


static u16_t
sensorentry_length(void* addr_inf, u8_t level)
{
  struct sensor_inf* sensors = addr_inf;

  if (level == 0)
  {
    /* one object (temperature) */
    return 1;
  }
  else if (level == 1)
  {
    /* number of sensor indexes */
    return sensors->sensor_list_rn.count;
  }
  else
  {
    return 0;
  }
}

static s32_t
sensorentry_idcmp(void* addr_inf, u8_t level, u16_t idx, s32_t sub_id)
{
  struct sensor_inf* sensors = addr_inf;
  
  if (level == 0)
  {
    return ((s32_t)(idx + 1) - sub_id);
  }
  else if (level == 1)
  {
    struct mib_list_node *ln;
    u16_t i;
  
    i = 0;
    ln = sensors->sensor_list_rn.head;
    while (i < idx)
    {
      i++;
      ln = ln->next;
    }
    LWIP_ASSERT("ln != NULL", ln != NULL);
    return (ln->objid - sub_id);
  }
  else
  {
    return -1;
  }
}

static void
sensorentry_get_subid(void* addr_inf, u8_t level, u16_t idx, s32_t *sub_id)
{
  struct sensor_inf* sensors = addr_inf;

  if (level == 0)
  {
    *sub_id = idx + 1;
  }
  else if (level == 1)
  {
    struct mib_list_node *ln;
    u16_t i;

    i = 0;
    ln = sensors->sensor_list_rn.head;
    while (i < idx)
    {
      i++;
      ln = ln->next;
    }
    LWIP_ASSERT("ln != NULL", ln != NULL);
    *sub_id = ln->objid;
  }
}

/**
 * Async question for object definition
 */
static void
sensorentry_get_object_def_q(void* addr_inf, u8_t rid, u8_t ident_len, s32_t *ident)
{
  u16_t sensor_register, sensor_address;

  ident_len += 1;
  ident -= 1;

  /* send request */
  sensor_register = ident[0];
  sensor_address = ident[1];
  LWIP_DEBUGF(SNMP_MIB_DEBUG,("sensor_request reg=%"U16_F" addr=%"U16_F"\n",
                              (u16_t)sensor_register, (u16_t)sensor_address));
  /* fake async quesion/answer */
  snmp_msg_event(rid);
}

static void
sensorentry_get_object_def_a(u8_t rid, u8_t ident_len, s32_t *ident, struct obj_def *od)
{
  /* return to object name, adding index depth (1) */
  ident_len += 1;
  ident -= 1;
  if (ident_len == 2)
  { 
    od->id_inst_len = ident_len;
    od->id_inst_ptr = ident;

    od->instance = MIB_OBJECT_TAB;
    od->access = MIB_OBJECT_READ_ONLY;
    od->asn_type = (SNMP_ASN1_UNIV | SNMP_ASN1_PRIMIT | SNMP_ASN1_INTEG);
    od->v_len = sizeof(s32_t);
  }
  else
  {
    LWIP_DEBUGF(SNMP_MIB_DEBUG,("sensorentry_get_object_def_a: no scalar\n"));
    od->instance = MIB_OBJECT_NONE;
  }
}

static void
sensorentry_get_object_def_pc(u8_t rid, u8_t ident_len, s32_t *ident)
{
  /* nop */
}

static void
sensorentry_get_value_q(u8_t rid, struct obj_def *od)
{
  /* fake async quesion/answer */
  snmp_msg_event(rid);
}

static void
sensorentry_get_value_a(u8_t rid, struct obj_def *od, u16_t len, void *value)
{
  u8_t i;
  s32_t *temperature = value;
  FILE* sensf;
  char senspath[sizeof(SENSORS_DIR)+1+SENSOR_NAME_LEN+1] = SENSORS_DIR"/";

  i = od->id_inst_ptr[1];
  strncpy(&senspath[sizeof(SENSORS_DIR)],
          sensor_addr_inf.sensor_files[i],
          SENSOR_NAME_LEN);
  sensf = fopen(senspath,"r");
  if (sensf != NULL)
  {
    fscanf(sensf,"%"S32_F,temperature);
    fclose(sensf);
  }
}

static void
sensorentry_get_value_pc(u8_t rid, struct obj_def *od)
{
  /* nop */
}

static void
sensorentry_set_test_q(u8_t rid, struct obj_def *od)
{
  /* fake async quesion/answer */
  snmp_msg_event(rid);
}

static u8_t
sensorentry_set_test_a(u8_t rid, struct obj_def *od, u16_t len, void *value)
{
  /* sensors are read-only */
  return 0;
}

static void
sensorentry_set_test_pc(u8_t rid, struct obj_def *od)
{
  /* nop */
}

static void
sensorentry_set_value_q(u8_t rid, struct obj_def *od, u16_t len, void *value)
{
  /* fake async quesion/answer */
  snmp_msg_event(rid);
}

static void
sensorentry_set_value_a(u8_t rid, struct obj_def *od, u16_t len, void *value)
{
}

static void
sensorentry_set_value_pc(u8_t rid, struct obj_def *od)
{
  /* nop */
}
