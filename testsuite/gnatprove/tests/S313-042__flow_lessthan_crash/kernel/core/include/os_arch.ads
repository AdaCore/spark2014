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
--  Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
--
--  @file os_arch.ads
--  @author Jean-Christophe Dubois (jcd@tribudubois.net)
--  @brief External arch specific functions
--

pragma Ada_2012;
pragma Style_Checks (Off);
pragma SPARK_Mode;

with types;
with Moth;

package os_arch is

   function interrupt_is_pending return types.uint8_t
      with Global => null;
   pragma Import (C, interrupt_is_pending, "os_arch_interrupt_is_pending");

   procedure idle
      with Global => null;
   pragma Import (C, idle, "os_arch_idle");

   procedure context_create (task_id : Moth.os_task_id_param_t)
      with Global => null;
   pragma Import (C, context_create, "os_arch_context_create");

   procedure context_switch (prev_id : Moth.os_task_id_param_t;
                             next_id : Moth.os_task_id_param_t)
      with Global => null;
   pragma Import (C, context_switch, "os_arch_context_switch");

   procedure context_set (task_id : Moth.os_task_id_param_t)
      with Global => null;
   pragma Import (C, context_set, "os_arch_context_set");

   procedure space_init
      with Global => null;
   pragma Import (C, space_init, "os_arch_space_init");

   procedure space_switch (old_context_id : Moth.os_task_id_param_t;
                           new_context_id : Moth.os_task_id_param_t)
      with Global => null;
   pragma Import (C, space_switch, "os_arch_space_switch");

   procedure cons_init
      with Global => null;
   pragma Import (C, cons_init, "os_arch_cons_init");

end os_arch;
