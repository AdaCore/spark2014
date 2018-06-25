--  PantherChess - based on AdaChess Copyright (C) 2017-2018 Bill Zuercher
--
--  AdaChess - Cool Chess Engine
--
--  Copyright (C) 2013-2017 - Alessandro Iavicoli
--  Email: adachess@gmail.com - Web Page: http://www.adachess.com
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.
--
--  This program is distributed in the hope that it will be useful,
--  but WITHOUT ANY WARRANTY; without even the implied warranty of
--  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
--  GNU General Public License for more details.
--
--  You should have received a copy of the GNU General Public License
--  along with this program.  If not, see <http://www.gnu.org/licenses/>.



with Ada.Task_Identification;

with System.Multiprocessors;
with System.Multiprocessors.Dispatching_Domains;

with Interfaces;

package ACMultiprocessor is


   CPU_Vendor : String (1 .. 12) := (others => ' ');

   --------------
   -- Wrappers --
   --------------

   subtype CPU_Range is System.Multiprocessors.CPU_Range;

   Number_Of_CPUs : constant System.Multiprocessors.CPU_Range := System.Multiprocessors.Number_Of_CPUs;
   Not_A_Specific_CPU : constant System.Multiprocessors.CPU_Range := System.Multiprocessors.Not_A_Specific_CPU;

   procedure Set_CPU
     (CPU     : CPU_Range;
      Task_Id : Ada.Task_Identification.Task_Id)
      renames System.Multiprocessors.Dispatching_Domains.Set_CPU;

   subtype Register_Type is Interfaces.Unsigned_32;

end ACMultiprocessor;
