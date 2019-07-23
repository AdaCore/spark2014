--
--  Copyright (c) 2017 Jean-Christophe Dubois
--  All rights reserved.
--
--  This program is free software; you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation; either version 2, or (at your option)
--  any later version.
--
--  This program is distributed in the hope that it will be useful,
--  but WITHOUT ANY WARRANTY; without even the implied warranty of
--  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
--  GNU General Public License for more details.
--
--  You should have received a copy of the GNU General Public License
--  along with this program; if not, write to the Free Software
--  Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.  --
--  @file
--  @author Jean-Christophe Dubois (jcd@tribudubois.net)
--  @brief
--

pragma Ada_2012;
pragma Style_Checks (Off);

with types;

package test with
   SPARK_mode
is

   OS_INTERRUPT_TASK_ID : constant := 0;

   OS_TASK_ID_NONE      : constant := -1;
   OS_TASK_ID_ALL       : constant := -2;

   OS_MBX_MASK_ALL      : constant := 16#ffffffff#;

   OS_SUCCESS           : constant := 0;
   OS_ERROR_FIFO_FULL   : constant := -1;
   OS_ERROR_FIFO_EMPTY  : constant := -2;
   OS_ERROR_DENIED      : constant := -3;
   OS_ERROR_RECEIVE     : constant := -4;
   OS_ERROR_PARAM       : constant := -5;
   OS_ERROR_MAX         : constant := OS_ERROR_PARAM;

   OS_MAX_TASK_CNT      : constant := 5;
   OS_MAX_TASK_ID       : constant := OS_MAX_TASK_CNT - 1;
   OS_MIN_TASK_ID       : constant := 0;

   OS_MBX_MSG_SZ        : constant := 32;

   subtype os_mbx_mask_t is types.uint32_t;

   subtype os_task_dest_id_t is types.int8_t
                           range OS_TASK_ID_ALL .. OS_MAX_TASK_ID;

   subtype os_task_id_t is os_task_dest_id_t
                           range OS_TASK_ID_NONE .. OS_MAX_TASK_ID;

   subtype os_task_id_param_t is os_task_id_t
                           range OS_MIN_TASK_ID .. OS_MAX_TASK_ID;

   subtype os_status_t is types.int32_t
                           range OS_ERROR_MAX .. OS_SUCCESS;

   type os_mbx_msg_t is range 0 .. 2 ** OS_MBX_MSG_SZ - 1;
   for os_mbx_msg_t'Size use OS_MBX_MSG_SZ;

   type os_mbx_entry_t is record
      sender_id        : os_task_id_t;
      msg              : os_mbx_msg_t;
   end record;
   pragma Convention (C_Pass_By_Copy, os_mbx_entry_t);

   function os_ghost_mbx_are_well_formed return Boolean
   with
      Ghost => true;

   procedure os_mbx_receive (status    : out os_status_t;
                             mbx_entry : out os_mbx_entry_t)
   with
      Pre =>
             os_ghost_mbx_are_well_formed,
      Post => os_ghost_mbx_are_well_formed;
   pragma Export (C, os_mbx_receive, "os_mbx_receive");

end test;
