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
--  @file moth-config.adb
--  @author Jean-Christophe Dubois (jcd@tribudubois.net)
--  @brief Moth static configuration
--

package body Moth.Config with
   Spark_Mode     => On,
   Refined_State => (State => (read_only_conf))
is
   subtype os_virtual_address_t is types.uint32_t;

   subtype os_size_t is types.uint32_t;

   type os_task_section_t is record
      virtual_address : os_virtual_address_t;
      size            : os_size_t;
   end record;
   pragma Convention (C_Pass_By_Copy, os_task_section_t);

   type os_task_ro_t is record
      priority       : os_priority_t;
      mbx_permission : os_mbx_mask_t;
      text           : os_task_section_t;
      bss            : os_task_section_t;
      stack          : os_task_section_t;
   end record;
   pragma Convention (C_Pass_By_Copy, os_task_ro_t);

   --------------------
   -- read_only_conf --
   --------------------

   read_only_conf : constant array (os_task_id_param_t) of os_task_ro_t;
   pragma Import (C, read_only_conf, "os_task_ro");

   ------------------------
   -- get_mbx_permission --
   ------------------------

   function get_mbx_permission
      (task_id : os_task_id_param_t) return os_mbx_mask_t is
      (read_only_conf (task_id).mbx_permission);

   -----------------------
   -- get_task_priority --
   -----------------------

   function get_task_priority
     (task_id : os_task_id_param_t) return os_priority_t is
     (read_only_conf (task_id).priority);

end Moth.Config;
