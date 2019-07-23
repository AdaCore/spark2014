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
--  @file moth-scheduler.adb
--  @author Jean-Christophe Dubois (jcd@tribudubois.net)
--  @brief Moth Scheduler subsystem
--

with Interfaces;   use Interfaces;
with Interfaces.C; use Interfaces.C;

with os_arch;
with Moth.Config;

separate (Moth) package body Scheduler
with
   SPARK_mode => on
is

   OS_INTERRUPT_TASK_ID : constant := 0;

   -----------------
   -- Private API --
   -----------------

   -----------------------
   -- Private variables --
   -----------------------

   -----------------------
   -- next_task --
   -----------------------

   next_task : array (os_task_id_param_t) of os_task_id_t;

   -----------------------
   -- prev_task --
   -----------------------

   prev_task : array (os_task_id_param_t) of os_task_id_t;

   -----------------------------
   -- task_list_head --
   -----------------------------
   --  This variable holds the ID of the first task in the ready list (the
   --  next one that will be elected).
   --  Note: Its value could be OS_TASK_ID_NONE if no task is ready.

   task_list_head : os_task_id_t;

   --------------
   -- mbx_mask --
   --------------

   mbx_mask : array (os_task_id_param_t) of os_mbx_mask_t;

   ------------------
   -- current_task --
   ------------------

   current_task : os_task_id_param_t;

   package body M is

      function "<" (Left, Right : os_task_id_param_t) return Boolean is
         (Moth.Config.get_task_priority (Left)
               < Moth.Config.get_task_priority (Right));

      function "=" (X, Y : T) return Boolean is
         (X.Idle = Y.Idle and then X.Ready = Y.Ready);

      function os_ghost_task_list_is_well_formed return Boolean is
        (Length (Model.Idle) <= OS_MAX_TASK_CNT and then
         Length (Model.Ready) <= OS_MAX_TASK_CNT and then
         Length (Model.Idle) + Length (Model.Ready) = OS_MAX_TASK_CNT and then
         (if Length (Model.Ready) = 0
             then task_list_head = OS_TASK_ID_NONE
             else task_list_head = First_Element (Model.Ready) and
                  prev_task (First_Element (Model.Ready)) = OS_TASK_ID_NONE) and then
         (for all task_id of Model.Ready =>
              next_task (task_id) =
                 (if task_id = Last_Element (Model.Ready)
                    then OS_TASK_ID_NONE
                    else Element (Model.Ready, Next (Model.Ready, Find (Model.Ready, task_id)))) and then
              prev_task (task_id) =
                 (if task_id = First_Element (Model.Ready)
                    then OS_TASK_ID_NONE
                    else Element (Model.Ready, Previous (Model.Ready, Find (Model.Ready, task_id))))) and then
         (for all task_id in os_task_id_param_t =>
            (if Contains (Model.Ready, task_id)
               then not Contains (Model.Idle, task_id)
               else (Contains (Model.Idle, task_id) and then
                     next_task (task_id) = OS_TASK_ID_NONE and then
                     prev_task (task_id) = OS_TASK_ID_NONE))));

      procedure enable_task (task_id : os_task_id_param_t) is
      begin
         if Contains (Model.Idle, task_id) then
            pragma assert (not Contains (Model.Ready, task_id));
            Model.Idle := Remove (Model.Idle, task_id);
            Insert (Model.Ready, task_id);
         end if;
         pragma assert (Contains (Model.Ready, task_id));
         pragma assert (not Contains (Model.Idle, task_id));
      end enable_task;

      procedure disable_task (task_id : os_task_id_param_t) is
      begin
         if Contains (Model.Ready, task_id) then
            pragma assert (not Contains (Model.Idle, task_id));
            Model.Idle := Add (Model.Idle, task_id);
            Delete (Model.Ready, task_id);
         end if;
         pragma assert (Contains (Model.Idle, task_id));
         pragma assert (not Contains (Model.Ready, task_id));
      end disable_task;

   begin
      Clear (Model.Ready);
      pragma Assert (Length (Model.Idle) = 0);
      pragma Assert (Is_Empty (Model.Idle));
      for task_id in os_task_id_param_t loop
         pragma assert (not Contains (Model.Idle, task_id));
         pragma assert (not Contains (Model.Ready, task_id));
         Model.Idle := Add (Model.Idle, task_id);
         pragma Loop_Invariant (Length (Model.Ready) = 0);
         pragma Loop_Invariant (Integer (Length (Model.Idle)) = Natural (task_id) + 1);
         pragma Loop_Invariant (for all id2 in OS_TASK_ID_MIN .. task_id
                                   => Contains (Model.Idle, id2));
      end loop;
      pragma Assert (Length (Model.Idle) = OS_MAX_TASK_CNT);
   end M;

   ----------------------
   --  Ghost functions --
   ----------------------

   -------------------
   -- task_is_ready --
   -------------------

   function task_is_ready (task_id : os_task_id_param_t) return Boolean
   is (Contains (M.Model.Ready, task_id));

   ---------------------------
   -- current_task_is_ready --
   ---------------------------

   function current_task_is_ready return Boolean
   is (task_is_ready (current_task));

   ------------------------------
   -- task_list_is_well_formed --
   ------------------------------

   function task_list_is_well_formed return Boolean is
      (M.os_ghost_task_list_is_well_formed);

   ----------------------------
   -- add_task_to_ready_list --
   ----------------------------

   procedure add_task_to_ready_list (task_id : os_task_id_param_t)
   with
      Refined_Post => Contains (M.Model.Ready, task_id) and then
                      task_list_is_well_formed
   is
      index_id : os_task_id_t := task_list_head;
   begin

      if index_id = OS_TASK_ID_NONE then
         --  No task in the ready list. Add this task at list head
         next_task (task_id) := OS_TASK_ID_NONE;
         prev_task (task_id) := OS_TASK_ID_NONE;
         task_list_head := task_id;
      else
         while index_id /= OS_TASK_ID_NONE loop
            pragma Loop_Invariant (task_list_is_well_formed);
            -- At any step in the loop index_id needs to be ready
            if index_id = task_id then
               --  Already in the ready list, nothing to do
               exit;
            elsif Moth.Config.get_task_priority (task_id) >
                  Moth.Config.get_task_priority (index_id) then
               -- task_id is higher priority so it needs to be inserted before
               -- index_id
               declare
                  prev_id : constant os_task_id_t :=
                                            prev_task (index_id);
               begin
                  prev_task (index_id) := task_id;
                  prev_task (task_id) := prev_id;
                  next_task (task_id) := index_id;

                  if prev_id = OS_TASK_ID_NONE then
                     task_list_head := task_id;
                  else
                     next_task (prev_id) := task_id;
                  end if;

                  exit;
               end;
            elsif next_task (index_id) = OS_TASK_ID_NONE then

               next_task (index_id) := task_id;
               prev_task (task_id)  := index_id;
               next_task (task_id)  := OS_TASK_ID_NONE;

               exit;
            else
               index_id := next_task (index_id);
            end if;
         end loop;
      end if;

      M.enable_task (task_id);

   end add_task_to_ready_list;

   ---------------------------------
   -- remove_task_from_ready_list --
   ---------------------------------

   procedure remove_task_from_ready_list
     (task_id : os_task_id_param_t)
   with
      Pre =>  task_is_ready (task_id) and then
              task_list_is_well_formed,
      Post => Contains (M.Model.Idle, task_id) and then
              task_list_is_well_formed
   is
      next_id : constant os_task_id_t := next_task (task_id);
      prev_id : constant os_task_id_t := prev_task (task_id);
   begin

      next_task (task_id) := OS_TASK_ID_NONE;
      prev_task (task_id) := OS_TASK_ID_NONE;

      M.disable_task (task_id);

      if task_id = task_list_head then

         -- Set the new list head (the next from the removed task)
         -- Note: next_id could be set to OS_TASK_ID_NONE
         task_list_head := next_id;

         if next_id /= OS_TASK_ID_NONE then

            -- The new list head [next] has no prev
            prev_task (next_id) := OS_TASK_ID_NONE;

         end if;

      else
         --  The list is not empty and the task is not at the list head.

         --  link next from prev task to our next
         next_task (prev_id) := next_id;

         if next_id /= OS_TASK_ID_NONE then

            --  link prev from next task to our prev
            prev_task (next_id) := prev_id;

         end if;

      end if;

   end remove_task_from_ready_list;

   --------------
   -- schedule --
   --------------

   procedure schedule (task_id : out os_task_id_param_t)
   with
      Pre => task_list_is_well_formed,
      Post => task_is_ready (task_id) and then
              task_list_head = task_id and then
              task_list_is_well_formed
   is
   begin
      --  Check interrupt status
      if os_arch.interrupt_is_pending = 1 then
         --  Put interrupt task in ready list if int is set.
         add_task_to_ready_list (OS_INTERRUPT_TASK_ID);
      end if;

      while task_list_head = OS_TASK_ID_NONE loop

         pragma Loop_Invariant (task_list_is_well_formed);

         --  No task is elected:
         --  Put processor in idle mode and wait for interrupt.
         os_arch.idle;

         --  Check interrupt status
         if os_arch.interrupt_is_pending = 1 then
            --  Put interrupt task in ready list if int is set.
            add_task_to_ready_list (OS_INTERRUPT_TASK_ID);
         end if;
      end loop;

      task_id := task_list_head;

      --  Select the elected task as current task.
      current_task := task_id;

      --  Return the ID of the elected task to allow context switch at low
      --  (arch) level
   end schedule;

   ----------------
   -- Public API --
   ----------------

   -------------------------
   -- get_current_task_id --
   -------------------------

   function get_current_task_id return os_task_id_param_t is
      (current_task);

   ------------------
   -- get_mbx_mask --
   ------------------

   function get_mbx_mask (task_id : os_task_id_param_t) return os_mbx_mask_t is
      (mbx_mask (task_id));

   ----------
   -- wait --
   ----------

   procedure wait
     (task_id      : out os_task_id_param_t;
      waiting_mask : in  os_mbx_mask_t)
   is
      tmp_mask : os_mbx_mask_t;
   begin
      task_id := current_task;

      tmp_mask := waiting_mask and Moth.Config.get_mbx_permission (task_id);

      --  We remove the current task from the ready list.
      remove_task_from_ready_list (task_id);

      if tmp_mask /= 0 then
         mbx_mask (task_id) := tmp_mask;

         tmp_mask := tmp_mask and Moth.Mailbox.os_mbx_get_posted_mask (task_id);

         if tmp_mask /= 0 then
            --  If waited event is already here, put the task back in the
            --  ready list (after tasks of same priority).
            add_task_to_ready_list (task_id);
         end if;
      elsif task_id /= OS_INTERRUPT_TASK_ID then
         --  This is an error/illegal case. There is nothing to wait for,
         --  so put the task back in the ready list.
         add_task_to_ready_list (task_id);
      end if;

      --  Let's elect the new running task.
      schedule (task_id);
   end wait;

   -----------
   -- yield --
   -----------

   procedure yield (task_id : out os_task_id_param_t)
   is
   begin
      task_id := current_task;

      --  We remove the current task from the ready list.
      remove_task_from_ready_list (task_id);

      --  We insert it back after the other tasks with same priority.
      add_task_to_ready_list (task_id);

      --  Let's elect the new running task.
      schedule (task_id);
   end yield;

   ---------------
   -- task_exit --
   ---------------

   procedure task_exit (task_id : out os_task_id_param_t)
   is
   begin
      task_id := current_task;

      --  Remove the current task from the ready list.
      remove_task_from_ready_list (task_id);

      --  Let's elect the new running task.
      schedule (task_id);
   end task_exit;

   ----------
   -- init --
   ----------

   procedure init (task_id : out os_task_id_param_t)
   is
      prev_id : os_task_id_param_t := os_task_id_param_t'First;
   begin

      --  Init the MMU
      os_arch.space_init;

      --  Init the task list head to NONE
      task_list_head := OS_TASK_ID_NONE;

      --  Init the task entry for one task
      next_task := (others => OS_TASK_ID_NONE);
      prev_task := (others => OS_TASK_ID_NONE);

      -- All Mbx mask for tasks are 0
      mbx_mask := (others => 0);

      for task_iterator in os_task_id_param_t'Range loop
         --  Initialise the memory space for one task
         os_arch.space_switch (prev_id, task_iterator);

         --  create the run context (stak, ...) for this task
         os_arch.context_create (task_iterator);

         --  Add the task to the ready list
         add_task_to_ready_list (task_iterator);

         prev_id := task_iterator;
      end loop;

      --  Select the task to run
      schedule (task_id);

      --  Set the selected task as the current one
      os_arch.context_set (task_id);

      --  Switch to this task context
      os_arch.space_switch (prev_id, task_id);
   end init;

end Scheduler;
