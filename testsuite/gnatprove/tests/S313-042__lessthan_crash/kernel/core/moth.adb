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
--  @file moth.adb
--  @author Jean-Christophe Dubois (jcd@tribudubois.net)
--  @brief Moth base name space
--

with os_arch;

package body Moth with
   Spark_Mode     => On
is

   ----------------------------
   -- Global Ghost functions --
   ----------------------------

   function os_ghost_mbx_are_well_formed return Boolean is
      (Moth.Mailbox.mbx_are_well_formed);

   function os_ghost_task_list_is_well_formed return Boolean is
      (Moth.Scheduler.task_list_is_well_formed);

   function os_ghost_current_task_is_ready return Boolean is
      (Moth.Scheduler.current_task_is_ready);

   function os_ghost_task_is_ready
                     (task_id : in os_task_id_param_t) return Boolean is
      (Moth.Scheduler.task_is_ready(task_id));

   package body Scheduler is separate;

   package body Mailbox is separate;

   procedure init (task_id : out os_task_id_param_t) is
   begin
      --  Init the console if any
      os_arch.cons_init;

      --  Init all mailboxes
      Moth.Mailbox.init;

      --  Init the task list.
      Moth.Scheduler.init (task_id);

   end init;

end Moth;
