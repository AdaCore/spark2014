------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                              O U T P U T S                               --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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

package body Outputs is

   procedure I  (O : Output_Id);
   --  If a new line has just been created, print as many spaces
   --  as the indentation level requires.

   function File_Handle (O : Output_Id) return File_Type;
   --  Return the file handle corresponding to this output id

   function File_Handle (O : Output_Id) return File_Type is
      (case O is
          when Stdout =>
             Standard_Output,
          when Stderr =>
             Standard_Error,
          when Current_File =>
             Current_File_Handle);

   ------------------------
   -- Close_Current_File --
   ------------------------

   procedure Close_Current_File is
   begin
      Close (Current_File_Handle);
      Output_States (Current_File).Indent := 0;
      Output_States (Current_File).New_Line := False;
   end Close_Current_File;

   -------
   -- I --
   -------

   procedure I (O : Output_Id) is
   begin
      if Output_States (O).New_Line then
         for J in 1 .. Output_States (O).Indent loop
            Put (File_Handle (O), " ");
         end loop;
         Output_States (O).New_Line := False;
      end if;
   end I;

   --------
   -- NL --
   --------

   procedure NL (O : Output_Id) is
   begin
      New_Line (File_Handle (O));
      Output_States (O).New_Line := True;
   end NL;

   -----------------------
   -- Open_Current_File --
   -----------------------

   procedure Open_Current_File (Filename : String) is
   begin
      Create (Current_File_Handle, Out_File, Filename);
      Output_States (Current_File).Indent := 0;
      Output_States (Current_File).New_Line := False;
   end Open_Current_File;

   -------
   -- P --
   -------

   procedure P  (O : Output_Id; S : String; As_String : Boolean := False) is
   begin
      I (O);
      if As_String then
         Put (File_Handle (O), '"');
         for I in S'Range loop
            if S (I) = '"' then
               Put (File_Handle (O), "\""");
            else
               Put (File_Handle (O), S (I));
            end if;
         end loop;
         Put (File_Handle (O), '"');
      else
         Put (File_Handle (O), S);
      end if;
   end P;

   --------
   -- PL --
   --------

   procedure PL (O : Output_Id; S : String) is
   begin
      I (O);
      Put_Line (File_Handle (O), S);
      Output_States (O).New_Line := True;
   end PL;

   ---------------------
   -- Relative_Indent --
   ---------------------

   procedure Relative_Indent
     (O    : Output_Id;
      Diff : Integer) is
   begin
      Output_States (O).Indent :=
        Natural (Output_States (O).Indent + Diff);
   end Relative_Indent;

   ---------------------
   -- Absolute_Indent --
   ---------------------

   procedure Absolute_Indent
     (O     : Output_Id;
      Level : Natural) is
   begin
      Output_States (O).Indent := Level;
   end Absolute_Indent;

end Outputs;
