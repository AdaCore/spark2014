------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                       N A M E D _ S E M A P H O R E S                    --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2019-2020, AdaCore                     --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that  it will be useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General Public License  distributed with  gnatprove;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with Interfaces.C; use Interfaces.C;

package body Named_Semaphores is

   function Create_Semaphore_C
     (Name : char_array; Init : unsigned) return Semaphore
   with Import, Convention => C, External_Name => "create_semaphore";

   function Open_Semaphore_C (Name : char_array) return Semaphore
   with Import, Convention => C, External_Name => "open_semaphore";

   procedure Close_Semaphore_C (S : Semaphore)
   with Import, Convention => C, External_Name => "close_semaphore";

   procedure Wait_Semaphore_C (S : Semaphore)
   with Import, Convention => C, External_Name => "wait_semaphore";

   procedure Release_Semaphore_C (S : Semaphore)
   with Import, Convention => C, External_Name => "release_semaphore";

   procedure Delete_Semaphore_C (Name : char_array)
   with Import, Convention => C, External_Name => "delete_semaphore";

   -----------
   -- Close --
   -----------

   procedure Close (S : in out Semaphore) is
   begin
      Close_Semaphore_C (S);
   end Close;

   ------------
   -- Create --
   ------------

   procedure Create (Name : String; Init : Natural; S : out Semaphore)
   is
   begin
      S := Create_Semaphore_C (To_C (Name), unsigned (Init));
   end Create;

   ------------
   -- Delete --
   ------------

   procedure Delete (Name : String) is
   begin
      Delete_Semaphore_C (To_C (Name));
   end Delete;

   ----------
   -- Open --
   ----------

   procedure Open (Name : String; S : out Semaphore) is
   begin
      S := Open_Semaphore_C (To_C (Name));
   end Open;

   -------------
   -- Release --
   -------------

   procedure Release (S : in out Semaphore) is
   begin
      Release_Semaphore_C (S);
   end Release;

   ----------
   -- Wait --
   ----------

   procedure Wait (S : in out Semaphore) is
   begin
      Wait_Semaphore_C (S);
   end Wait;

end Named_Semaphores;
