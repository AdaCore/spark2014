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
--  @file moth-config.ads
--  @author Jean-Christophe Dubois (jcd@tribudubois.net)
--  @brief Moth static configuration accessors
--

package Moth.Config with
   Spark_Mode     => On,
   Abstract_State => State
is

   subtype os_priority_t is types.uint8_t;

   ---------------------------------------------
   -- Get the MBX permission for a given task --
   ---------------------------------------------

   function get_mbx_permission
      (task_id : os_task_id_param_t) return os_mbx_mask_t with
       Global => (Input => State);

   ---------------------------------------
   -- Get the priority for a given task --
   ---------------------------------------

   function get_task_priority
     (task_id : os_task_id_param_t) return os_priority_t with
      Global => (Input => State);

end Moth.Config;
