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
--  @file moth-mailbox.adb
--  @author Jean-Christophe Dubois (jcd@tribudubois.net)
--  @brief Moth Mailbox subsytem
--

with Interfaces;   use Interfaces;
with Interfaces.C; use Interfaces.C;

with Moth.Config;

separate (Moth) package body Mailbox with
   SPARK_mode => On
is

   -----------------
   -- Private API --
   -----------------

   -------------------
   -- Private types --
   -------------------

   -- Max mbx count is provided through configuration
   OS_MAX_MBX_CNT      : constant := OpenConf.CONFIG_TASK_MBX_COUNT;

   -- Type to define a mbx index
   type os_mbx_index_t is mod OS_MAX_MBX_CNT;

   -- Type to define the number of mbx in the task FIFO
   subtype os_mbx_count_t is types.uint8_t range 0 .. OS_MAX_MBX_CNT;

   -- Type to define the task FIFO
   type os_mbx_t_array is array (os_mbx_index_t) of os_mbx_entry_t;

   -- This structure allows to manage mbx for one task
   type os_mbx_t is record
      head             : os_mbx_index_t;
      count            : os_mbx_count_t;
      mbx_array        : os_mbx_t_array;
   end record;

   -----------------------
   -- Private variables --
   -----------------------

   mbx_fifo : array (os_task_id_param_t) of os_mbx_t;

   ----------------------------------
   -- Private functions/procedures --
   ----------------------------------

   ----------------------
   -- + os_mbx_index_t --
   ----------------------
   -- add operator overload for os_mbx_index_t

   function "+" (Left  : os_mbx_index_t;
                 Right : os_mbx_count_t) return os_mbx_index_t
   is (Left + os_mbx_index_t'Mod (Right));

   ---------------------
   -- mbx_is_empty --
   ---------------------
   --  Check if the mbx fifo of a given task is empty.

   function mbx_is_empty (task_id : os_task_id_param_t) return Boolean
   is (mbx_fifo (task_id).count = os_mbx_count_t'First);

   --------------------
   -- mbx_is_full --
   --------------------
   --  Check if the mbx fifo of a given task is full.

   function mbx_is_full (task_id : os_task_id_param_t) return Boolean
   is (mbx_fifo (task_id).count = os_mbx_count_t'Last);

   -------------------------
   -- get_mbx_head --
   -------------------------
   --  Retrieve the mbx head index of the given task.

   function get_mbx_head
     (task_id : os_task_id_param_t) return os_mbx_index_t
   is (mbx_fifo (task_id).head);

   -------------------
   -- get_mbx_count --
   -------------------
   --  Retrieve the mbx count of the given task.

   function get_mbx_count
     (task_id : os_task_id_param_t) return os_mbx_count_t
   is (mbx_fifo (task_id).count);

   ------------------
   -- get_mbx_tail --
   ------------------
   --  Retrieve the mbx tail index of the given task.

   function get_mbx_tail
     (task_id : os_task_id_param_t) return os_mbx_index_t
   is (get_mbx_head (task_id) +
       os_mbx_count_t'Pred (get_mbx_count (task_id)))
   with
      Pre => not mbx_is_empty (task_id);

   ---------------------
   -- mbx_add_message --
   ---------------------
   --  Add a mbx to the mbx fifo of a given task.

   procedure mbx_add_message
     (dest_id : os_task_id_param_t;
      src_id  : os_task_id_param_t;
      mbx_msg : os_mbx_msg_t)
   with
      Pre  => ((not mbx_is_full (dest_id)) and then
               mbx_are_well_formed),
      Post => ((not mbx_is_empty (dest_id)) and then
               (mbx_fifo = mbx_fifo'Old'Update (dest_id => mbx_fifo'Old (dest_id)'Update (count => mbx_fifo'Old (dest_id).count + 1, head => mbx_fifo'Old (dest_id).head, mbx_array => mbx_fifo'Old (dest_id).mbx_array'Update (get_mbx_tail (dest_id) => mbx_fifo'Old (dest_id).mbx_array (get_mbx_tail (dest_id))'Update (sender_id => src_id, msg => mbx_msg))))) and then
               mbx_are_well_formed)
   is
      mbx_index : constant os_mbx_index_t := get_mbx_head (dest_id) + get_mbx_count (dest_id);
   begin
      mbx_fifo (dest_id).count :=  os_mbx_count_t'Succ (mbx_fifo (dest_id).count);
      mbx_fifo (dest_id).mbx_array (mbx_index).sender_id := src_id;
      mbx_fifo (dest_id).mbx_array (mbx_index).msg := mbx_msg;
   end mbx_add_message;

   --------------------------
   -- get_mbx_entry_sender --
   --------------------------

   function get_mbx_entry_sender
     (task_id : os_task_id_param_t;
      index   : os_mbx_count_t) return os_task_id_param_t
   is (os_task_id_param_t (mbx_fifo (task_id).mbx_array
           (get_mbx_head (task_id) + index).sender_id))
   with
      Pre => mbx_fifo (task_id).mbx_array
                  (get_mbx_head (task_id) + index).sender_id
                  in os_task_id_param_t;

   ----------------------------
   -- os_mbx_get_posted_mask --
   ----------------------------

   function os_mbx_get_posted_mask
     (task_id : os_task_id_param_t) return os_mbx_mask_t
   is
      mbx_mask  : os_mbx_mask_t := 0;
   begin

      if not mbx_is_empty (task_id) then
         for iterator in 0 ..
                         os_mbx_count_t'Pred (get_mbx_count (task_id))
         loop
             mbx_mask := mbx_mask or
              os_mbx_mask_t (Shift_Left (Unsigned_32'(1),
                                         Natural (
                                            get_mbx_entry_sender (task_id,
                                                                  iterator))));
         end loop;
      end if;

      return mbx_mask;
   end os_mbx_get_posted_mask;

   -------------------
   -- send_one_task --
   -------------------

   procedure send_one_task
     (status  : out os_status_t;
      dest_id : in  os_task_id_param_t;
      mbx_msg : in  os_mbx_msg_t)
   with
      Pre => Moth.os_ghost_task_list_is_well_formed and
             mbx_are_well_formed,
      Post => Moth.os_ghost_task_list_is_well_formed and
              mbx_are_well_formed
   is
      current        : constant os_task_id_param_t :=
                                Moth.Scheduler.get_current_task_id;
      mbx_permission : constant os_mbx_mask_t :=
        Moth.Config.get_mbx_permission (dest_id) and
        os_mbx_mask_t (Shift_Left (Unsigned_32'(1), Natural (current)));
   begin
      if mbx_permission /= 0 then
         if mbx_is_full (dest_id) then
            status := OS_ERROR_FIFO_FULL;
         else
            mbx_add_message (dest_id, current, mbx_msg);
            if (Moth.Scheduler.get_mbx_mask (dest_id) and
               os_mbx_mask_t (Shift_Left (Unsigned_32'(1), Natural (current)))) /= 0 then
               Moth.Scheduler.add_task_to_ready_list (dest_id);
            end if;
            status := OS_SUCCESS;
         end if;
      else
         status := OS_ERROR_DENIED;
      end if;

   end send_one_task;

   -------------------
   -- send_all_task --
   -------------------

   procedure send_all_task
     (status  : out os_status_t;
      mbx_msg : in  os_mbx_msg_t)
   with
      Pre => Moth.os_ghost_task_list_is_well_formed and
             mbx_are_well_formed,
      Post => Moth.os_ghost_task_list_is_well_formed and
              mbx_are_well_formed
   is
      ret : os_status_t;
   begin
      status := OS_ERROR_DENIED;

      for iterator in os_task_id_param_t'Range loop
         send_one_task (ret, iterator, mbx_msg);

         if ret = OS_ERROR_FIFO_FULL then
            status := ret;
         else
            if status /= OS_ERROR_FIFO_FULL then
               if ret = OS_SUCCESS then
                  status := OS_SUCCESS;
               end if;
            end if;
         end if;
      end loop;
   end send_all_task;

   -------------------
   -- get_mbx_entry --
   -------------------

   function get_mbx_entry
     (task_id   : os_task_id_param_t;
      index : os_mbx_count_t) return os_mbx_entry_t
   is (mbx_fifo (task_id).mbx_array (get_mbx_head (task_id) + index));

   --------------------------
   -- is_waiting_mbx_entry --
   --------------------------

   function is_waiting_mbx_entry
     (task_id   : os_task_id_param_t;
      index : os_mbx_count_t) return Boolean
   is ((Moth.Scheduler.get_mbx_mask (task_id) and
        os_mbx_mask_t (Shift_Left
                (Unsigned_32'(1), Natural (get_mbx_entry_sender
                (task_id, index))))) /= 0)
   with
      Pre => (not mbx_is_empty (task_id)) and then
             mbx_are_well_formed and then
             index < get_mbx_count (task_id) and then
             get_mbx_entry_sender (task_id, index) in os_task_id_param_t;

   ----------------------
   --  Ghost functions --
   ----------------------

   -------------------------
   -- mbx_are_well_formed --
   -------------------------

   function mbx_are_well_formed return Boolean is
      (for all task_id in os_task_id_param_t'Range =>
         (for all index in os_mbx_index_t'Range =>
            (if (os_mbx_count_t(index) >= get_mbx_count (task_id))
               then (mbx_fifo (task_id).mbx_array (get_mbx_head (task_id) + index).sender_id = OS_TASK_ID_NONE)
               else (mbx_fifo (task_id).mbx_array (get_mbx_head (task_id) + index).sender_id in os_task_id_param_t))));

   ----------------
   -- Public API --
   ----------------

   ----------------------
   -- remove_first_mbx --
   ----------------------

   procedure remove_first_mbx
      (task_id    : in os_task_id_param_t)
   with
      Pre  => (not mbx_is_empty (task_id)) and mbx_are_well_formed,
      Post => (mbx_fifo = mbx_fifo'Old'Update (task_id => mbx_fifo'Old (task_id)'Update (count => os_mbx_count_t'Pred (mbx_fifo'Old (task_id).count), head => os_mbx_index_t'Succ (mbx_fifo'Old (task_id).head), mbx_array => mbx_fifo'Old (task_id).mbx_array'Update (os_mbx_index_t'Pred (get_mbx_head (task_id)) => (sender_id => OS_TASK_ID_NONE, msg => 0)))))
              and mbx_are_well_formed
   is
      mbx_index   : constant os_mbx_index_t := get_mbx_head (task_id);
   begin
      mbx_fifo (task_id).count := os_mbx_count_t'Pred (mbx_fifo (task_id).count);
      mbx_fifo (task_id).head := os_mbx_index_t'Succ (mbx_fifo (task_id).head);
      mbx_fifo (task_id).mbx_array (mbx_index).sender_id := OS_TASK_ID_NONE;
      mbx_fifo (task_id).mbx_array (mbx_index).msg := 0;
   end remove_first_mbx;

   ---------------------
   -- remove_last_mbx --
   ---------------------

   procedure remove_last_mbx
      (task_id    : in os_task_id_param_t)
   with
      Pre  => (not mbx_is_empty (task_id)) and mbx_are_well_formed,
      Post => (mbx_fifo = mbx_fifo'Old'Update (task_id => mbx_fifo'Old (task_id)'Update (count => os_mbx_count_t'Pred (mbx_fifo'Old (task_id).count), head => mbx_fifo'Old (task_id).head, mbx_array => mbx_fifo'Old (task_id).mbx_array'Update (mbx_fifo (task_id).head + mbx_fifo (task_id).count => (sender_id => OS_TASK_ID_NONE, msg => 0)))))
              and mbx_are_well_formed
   is
      mbx_index   : constant os_mbx_index_t := get_mbx_tail (task_id);
   begin
      mbx_fifo (task_id).count := os_mbx_count_t'Pred (mbx_fifo (task_id).count);
      mbx_fifo (task_id).mbx_array (mbx_index).sender_id := OS_TASK_ID_NONE;
      mbx_fifo (task_id).mbx_array (mbx_index).msg := 0;
   end remove_last_mbx;

   --------------------
   -- mbx_shift_down --
   --------------------

   procedure mbx_shift_down
      (task_id    : in os_task_id_param_t;
       index      : in os_mbx_count_t)
   with
      Pre => (not mbx_is_empty (task_id)) and
             mbx_are_well_formed and
             (index > 0) and
             (index < os_mbx_count_t'Pred (get_mbx_count (task_id))),
      Post => mbx_are_well_formed and
              mbx_fifo (task_id).count = mbx_fifo'Old (task_id).count and
              mbx_fifo (task_id).head = mbx_fifo'Old (task_id).head
   is
      mbx_index   : os_mbx_index_t;
   begin
      for iterator in index ..
                      os_mbx_count_t'Pred (get_mbx_count (task_id)) loop
         pragma Loop_Invariant (mbx_are_well_formed);

         mbx_index := get_mbx_head (task_id) + iterator;

         mbx_fifo (task_id).mbx_array (mbx_index) :=
            mbx_fifo (task_id).mbx_array (os_mbx_index_t'Succ (mbx_index));
      end loop;
   end mbx_shift_down;

   -------------
   -- receive --
   -------------

   procedure receive
     (status    : out os_status_t;
      mbx_entry : out os_mbx_entry_t)
   is
      --  retrieve current task id
      current   : constant os_task_id_param_t :=
                           Moth.Scheduler.get_current_task_id;
   begin

      mbx_entry.sender_id := OS_TASK_ID_NONE;
      mbx_entry.msg       := 0;

      if mbx_is_empty (current) then
         --  mbx queue is empty, so we return with error
         status := OS_ERROR_FIFO_EMPTY;
      else
         --  initialize status to error in case we don't find a mbx.
         status := OS_ERROR_RECEIVE;

         --  go through received mbx for the current task
         for iterator in 0 ..
                         os_mbx_count_t'Pred (get_mbx_count (current)) loop

            pragma Loop_Invariant (mbx_are_well_formed and
                                   (not mbx_is_empty (current)));

            -- This Loop Invariant is a work arround. The prover is unable
            -- to see that the code under the os_mbx_is_waiting_mbx_entry()
            -- branch has no impact on the loop as the branch exits
            -- unconditionnaly in all cases. This loop invariant allows the
            -- prover to work but it should be removed later when the prover
            -- supports branches with exit path.
            pragma Loop_Invariant (mbx_fifo =
                                         mbx_fifo'Loop_Entry);

            --  is this a mbx we are waiting for
            if is_waiting_mbx_entry (current, iterator) then

               --  copy the mbx into the task mbx entry
               mbx_entry := get_mbx_entry (current, iterator);

               if iterator = 0 then
                  --  This was the first mbx (aka mbx head )

                  --  Clear the first entry and increment the mbx head
                  remove_first_mbx (current);
               else
                  --  This was not the first MBX

                  --  Compact the mbx if necessary
                  if iterator <
                     os_mbx_count_t'Pred (get_mbx_count (current)) then
                     --  This is not the last MBX
                     --  For now we "compact" the rest of the mbx queue,
                     --  so that there is no "hole" in it for the next mbx
                     --  search.

                     mbx_shift_down (current, iterator);
                  end if;

                  --  remove the last mbx from the mbx queue
                  --  (by clearing the last entry and decreasing the
                  --  mbx count).
                  remove_last_mbx (current);
               end if;

               --  We found a matching mbx
               status := OS_SUCCESS;

               --  Exit the for loop as we found a mbx we were
               --  waiting for.
               exit;
            end if;
         end loop;
      end if;
   end receive;

   ----------
   -- send --
   ----------

   procedure send
     (status  : out os_status_t;
      dest_id : in  types.int8_t;
      mbx_msg : in  os_mbx_msg_t)
   is
      --  dest_id comes from uncontroled C calls (user space)
      --  We don't make assumptions on its value, so we are testing
      --  all cases.
   begin
      if dest_id = OS_TASK_ID_ALL then
         send_all_task (status, mbx_msg);
      elsif dest_id in os_task_id_param_t then
         send_one_task (status, dest_id, mbx_msg);
      else
         status := OS_ERROR_PARAM;
      end if;
   end send;

   ----------
   -- init --
   ----------

   procedure init is
   begin
      mbx_fifo := (others => (head  => os_mbx_index_t'First,
                              count => os_mbx_count_t'First,
                              mbx_array => (others =>
                                            (sender_id => OS_TASK_ID_NONE,
                                             msg => 0))));
   end init;

end Mailbox;
