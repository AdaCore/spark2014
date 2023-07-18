------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--          G N A T 2 W H Y - D A T A _ D E C O M P O S I T I O N           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2023, AdaCore                        --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Directories;
with Call;                       use Call;
with Common_Containers;          use Common_Containers;
with GNATCOLL.JSON;              use GNATCOLL.JSON;
with Namet;                      use Namet;
with Sinput;                     use Sinput;
with Types;                      use Types;
with VC_Kinds;                   use VC_Kinds;

package body Gnat2Why.Data_Decomposition is

   ---------------------------------------
   -- Read_Data_Decomposition_JSON_File --
   ---------------------------------------

   procedure Read_Data_Decomposition_JSON_File is

      procedure Handle_Entry (JSON_Entry : JSON_Value);
      --  Insert an entry in the map Data_Decomposition_Table

      function Handle_Field
        (JSON_Entry : JSON_Value; Field : String) return Optional_Int;
      --  Return the optional data decomposition entry corresponding to Field
      --  in JSON_Entry, when possible.

      ------------------
      -- Handle_Entry --
      ------------------

      procedure Handle_Entry (JSON_Entry : JSON_Value) is
         Location   : constant String := Get (JSON_Entry, "location");
         Data_Entry : Data_Decomposition_Entry;
      begin
         Data_Entry.Size        := Handle_Field (JSON_Entry, "Size");
         Data_Entry.Value_Size  := Handle_Field (JSON_Entry, "Value_Size");
         Data_Entry.Object_Size := Handle_Field (JSON_Entry, "Object_Size");
         Data_Entry.Alignment   := Handle_Field (JSON_Entry, "Alignment");

         --  Subunits ("separates") may lead to duplicate entries for the same
         --  type or object, in files for the subunit and the main unit.
         if Data_Decomposition_Table.Contains (Location)
           and then Data_Entry /= Data_Decomposition_Table.Element (Location)
         then
            raise Program_Error
              with "inconsistent data representation duplicate";
         end if;

         Data_Decomposition_Table.Include (Location, Data_Entry);
      end Handle_Entry;

      ------------------
      -- Handle_Field --
      ------------------

      function Handle_Field
        (JSON_Entry : JSON_Value; Field : String) return Optional_Int
      is
      begin
         --  We must check whether each value is of integer type, as the value
         --  "??" is used in -gnatR2 mode to indicate that the numerical value
         --  depends on back annotations by gigi, for variants of records whose
         --  size depends on discriminants or other values. See comments in
         --  repinfo.ads for details.

         if Has_Field (JSON_Entry, Field)
           and then Kind (Get (JSON_Entry, Field)) = JSON_Int_Type
         then
            return (Present => True, Value => Get (Get (JSON_Entry, Field)));
         else
            return (Present => False);
         end if;
      end Handle_Field;

      --  Local variables

      File_Names : String_Sets.Set;

   --  Start of processing for Read_Data_Decomposition_JSON_File

   begin
      for SFI in 1 .. Last_Source_File loop
         if Sinput.File_Type (SFI) = Src then
            declare
               Source_File_Name : constant String :=
                 Get_Name_String (File_Name (SFI));
               JSON_File_Name : constant String :=
                 Ada.Directories.Compose
                   (Containing_Directory => Data_Representation_Subdir_Name,
                    Name                 => Source_File_Name,
                    Extension            => "json");
            begin
               if not File_Names.Contains (Source_File_Name)
                 and then Ada.Directories.Exists (JSON_File_Name)
               then
                  declare
                     File    : constant JSON_Value :=
                       Read_File_Into_JSON (JSON_File_Name);
                     Entries : constant JSON_Array := Get (File);
                  begin
                     for Index in 1 .. Length (Entries) loop
                        Handle_Entry (Get (Entries, Index));
                     end loop;

                     File_Names.Insert (Source_File_Name);
                  end;
               end if;
            end;
         end if;
      end loop;
   end Read_Data_Decomposition_JSON_File;

end Gnat2Why.Data_Decomposition;
