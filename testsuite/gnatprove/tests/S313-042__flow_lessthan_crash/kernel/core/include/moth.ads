--
--  Copyright (c) 2019 Jean-Christophe Dubois
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
--  Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
--
--  @file moth.ads
--  @author Jean-Christophe Dubois (jcd@tribudubois.net)
--  @brief Moth base types and init function.
--

-- pragma Unevaluated_Use_Of_Old (Allow);

with Ada.Containers.Formal_Ordered_Sets;
with Ada.Containers.Functional_Sets;
with Ada.Containers;

use type Ada.Containers.Count_Type;

with types;
with OpenConf;

package Moth with
   Spark_Mode     => On
is
   ---------------------------
   -- os_task_id definition --
   ---------------------------

   OS_TASK_ID_NONE      : constant := -1;
   OS_TASK_ID_ALL       : constant := -2;

   OS_MAX_TASK_CNT      : constant := OpenConf.CONFIG_MAX_TASK_COUNT;
   OS_TASK_ID_MAX       : constant := OS_MAX_TASK_CNT - 1;
   OS_TASK_ID_MIN       : constant := 0;

   subtype os_task_dest_id_t is types.int8_t
                           range OS_TASK_ID_ALL .. OS_TASK_ID_MAX;

   subtype os_task_id_t is os_task_dest_id_t
                           range OS_TASK_ID_NONE .. OS_TASK_ID_MAX;

   subtype os_task_id_param_t is os_task_id_t
                           range OS_TASK_ID_MIN .. OS_TASK_ID_MAX;

   ----------------------------
   -- os_status_t definition --
   ----------------------------

   OS_SUCCESS          : constant := 0;
   OS_ERROR_FIFO_FULL  : constant := -1;
   OS_ERROR_FIFO_EMPTY : constant := -2;
   OS_ERROR_DENIED     : constant := -3;
   OS_ERROR_RECEIVE    : constant := -4;
   OS_ERROR_PARAM      : constant := -5;
   OS_ERROR_MAX        : constant := OS_ERROR_PARAM;

   subtype os_status_t is types.int32_t
                           range OS_ERROR_MAX .. OS_SUCCESS;

   ------------------------------
   -- os_mbx_mask_t definition --
   ------------------------------

   OS_MBX_MASK_ALL      : constant := 16#ffffffff#;

   subtype os_mbx_mask_t is types.uint32_t;

   ----------------------------
   -- Global Ghost functions --
   ----------------------------

   function os_ghost_mbx_are_well_formed return Boolean
   with
      Ghost => true;

   function os_ghost_task_list_is_well_formed return Boolean
   with
      Ghost => true;

   function os_ghost_current_task_is_ready return Boolean
   with
      Ghost => true;

   function os_ghost_task_is_ready
                     (task_id : in os_task_id_param_t) return Boolean
   with
      Ghost => true;

   -----------------------
   -- Scheduler package --
   -----------------------

   package Scheduler
   with
      SPARK_mode     => on
   is

      package M
      with
         Ghost,
         Initializes => Model,
         Initial_Condition =>
          (Length (Model.Ready) = 0 and then
           Length (Model.Idle) = OS_MAX_TASK_CNT and then
           (for all task_id in os_task_id_param_t =>
                               Contains (Model.Idle, task_id)))
      is

         function "<" (Left, Right : os_task_id_param_t) return Boolean;

         package S1 is new Ada.Containers.Formal_Ordered_Sets
            (Element_Type => os_task_id_param_t);
         use S1;

         package S2 is new Ada.Containers.Functional_Sets
            (Element_Type => os_task_id_param_t);
         use S2;

         type T is record
            -- Idle tasks are unordered. So they are modeled as a set
            Idle  : S2.Set;
            -- Ready tasks are ordered. So they are modeled as an ordered set
            Ready : S1.Set (OS_MAX_TASK_CNT);
         end record;

         function "=" (X, Y : T) return Boolean;

         Model : T;

         function os_ghost_task_list_is_well_formed return Boolean;

         procedure enable_task (task_id : os_task_id_param_t)
         with
            Pre => os_ghost_task_list_is_well_formed;

         procedure disable_task (task_id : os_task_id_param_t)
         with
            Pre => os_ghost_task_list_is_well_formed;

      end M;

      use M;
      use M.S1;
      use M.S2;


      ---------------------
      -- Ghost functions --
      ---------------------

      function task_list_is_well_formed return Boolean
      with
         Ghost => true;

      function current_task_is_ready return Boolean
      with
         Ghost => true;

      function task_is_ready
                        (task_id : in os_task_id_param_t) return Boolean
      with
         Ghost => true;

      -------------------------------------
      -- Function needed in Moth.Mailbox --
      -------------------------------------

      procedure add_task_to_ready_list (task_id : in os_task_id_param_t)
      with
         Pre    => Moth.os_ghost_task_list_is_well_formed,
         Post   => Moth.os_ghost_task_list_is_well_formed;

      ----------
      -- wait --
      ----------

      procedure wait (task_id      : out os_task_id_param_t;
                      waiting_mask :     os_mbx_mask_t)
      with
         Pre    => Moth.os_ghost_task_list_is_well_formed and
                   Moth.os_ghost_mbx_are_well_formed and
                   Moth.os_ghost_current_task_is_ready,
         Post   => Moth.os_ghost_task_list_is_well_formed and
                   Moth.os_ghost_mbx_are_well_formed and
                   Moth.os_ghost_task_is_ready (task_id);
      pragma Export (C, wait, "os_sched_wait");

      -----------
      -- yield --
      -----------

      procedure yield (task_id : out os_task_id_param_t)
      with
         Pre    => Moth.os_ghost_task_list_is_well_formed and
                   Moth.os_ghost_current_task_is_ready,
         Post   => Moth.os_ghost_task_list_is_well_formed and
                   Moth.os_ghost_task_is_ready (task_id);
      pragma Export (C, yield, "os_sched_yield");

      ---------------
      -- task_exit --
      ---------------

      procedure task_exit (task_id : out os_task_id_param_t)
      with
         Pre    => Moth.os_ghost_task_list_is_well_formed and
                   Moth.os_ghost_current_task_is_ready,
         Post   => Moth.os_ghost_task_list_is_well_formed and
                   Moth.os_ghost_task_is_ready (task_id);
      pragma Export (C, task_exit, "os_sched_exit");

      -------------------------
      -- get_current_task_id --
      -------------------------

      function get_current_task_id return os_task_id_param_t;
      pragma Export (C, get_current_task_id, "os_sched_get_current_task_id");

      ------------------
      -- get_mbx_mask --
      ------------------

      function get_mbx_mask (task_id : os_task_id_param_t) return os_mbx_mask_t;

      ----------
      -- init --
      ----------

      procedure init (task_id : out os_task_id_param_t)
      with
         Post   => Moth.os_ghost_task_list_is_well_formed;

   end Scheduler;

   ---------------------
   -- Mailbox package --
   ---------------------

   package Mailbox
   with
      SPARK_mode     => on
   is
      ------------------
      -- Public types --
      ------------------

      OS_MBX_MSG_SZ       : constant := OpenConf.CONFIG_MBX_SIZE;

      type os_mbx_msg_t is range 0 .. 2 ** OS_MBX_MSG_SZ - 1;
      for os_mbx_msg_t'Size use OS_MBX_MSG_SZ;

      type os_mbx_entry_t is record
         sender_id        : os_task_id_t;
         msg              : os_mbx_msg_t;
      end record;
      pragma Convention (C_Pass_By_Copy, os_mbx_entry_t);

      ---------------------
      -- Ghost functions --
      ---------------------

      function mbx_are_well_formed return Boolean
      with
         Ghost => true;

      ----------------------------
      -- os_mbx_get_posted_mask --
      ----------------------------

      function os_mbx_get_posted_mask
        (task_id : os_task_id_param_t) return os_mbx_mask_t
      with
         Pre    => Moth.os_ghost_mbx_are_well_formed;

      -----------------
      -- mbx_receive --
      -----------------

      procedure receive (status    : out os_status_t;
                         mbx_entry : out os_mbx_entry_t)
      with
         Pre    => Moth.os_ghost_mbx_are_well_formed,
         Post   => Moth.os_ghost_mbx_are_well_formed;
      pragma Export (C, receive, "os_mbx_receive");

      --------------
      -- mbx_send --
      --------------

      procedure send (status  : out os_status_t;
                      dest_id :     types.int8_t;
                      mbx_msg :     os_mbx_msg_t)
      with
         Pre    => Moth.os_ghost_mbx_are_well_formed and
                   Moth.os_ghost_task_list_is_well_formed,
         Post   => Moth.os_ghost_mbx_are_well_formed and
                   Moth.os_ghost_task_list_is_well_formed;
      pragma Export (C, send, "os_mbx_send");

      ----------
      -- init --
      ----------

      procedure init
      with
         Post   => Moth.os_ghost_mbx_are_well_formed;

   end Mailbox;

   procedure init (task_id : out os_task_id_param_t)
   with
      Post => Moth.os_ghost_mbx_are_well_formed and
              Moth.os_ghost_task_list_is_well_formed;
   pragma Export (C, init, "os_init");


end Moth;
