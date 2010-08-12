------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                              O U T P U T S                               --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute it and/or modify it   --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2why is distributed in the hope that it will  be  useful,   --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

package body Outputs is

   procedure I  (O : in out Output_Record);
   --  If a new line has just been created, print as many spaces
   --  as the indentation level requires.

   ------------------
   -- Close_Output --
   ------------------

   procedure Close_Output (O : in out Output_Record) is
   begin
      Close (O.File);
      O.Indent := 0;
      O.New_Line := False;
   end Close_Output;

   -------
   -- I --
   -------

   procedure I (O : in out Output_Record) is
   begin
      if O.New_Line then
         for J in 1 .. O.Indent loop
            Put (O.File, " ");
         end loop;
         O.New_Line := False;
      end if;
   end I;

   --------
   -- NL --
   --------

   procedure NL (O : in out Output_Record) is
   begin
      New_Line (O.File);
      O.New_Line := True;
   end NL;

   -----------------
   -- Open_Output --
   -----------------

   procedure Open_Output (O : in out Output_Record; Filename : String) is
   begin
      Create (O.File, Out_File, Filename);
      O.Indent := 0;
      O.New_Line := False;
   end Open_Output;

   -------
   -- P --
   -------

   procedure P  (O : in out Output_Record; S : Wide_String) is
   begin
      I (O);
      Put (O.File, S);
   end P;

   --------
   -- PL --
   --------

   procedure PL (O : in out Output_Record; S : Wide_String) is
   begin
      I (O);
      Put_Line (O.File, S);
      O.New_Line := True;
   end PL;

   ---------------
   -- Print_Box --
   ---------------

   procedure Print_Box
     (O               : in out Output_Record;
      Subprogram_Name : Wide_String)
   is
      procedure Print_Line;

      procedure Print_Line is
      begin
         P (O, "---");
         for J in Subprogram_Name'Range loop
            P (O, "-");
         end loop;
         PL (O, "---");
      end Print_Line;

   begin
      Print_Line;
      PL (O, "-- " & Subprogram_Name & " --");
      Print_Line;
   end Print_Box;

   ---------------------
   -- Relative_Indent --
   ---------------------

   procedure Relative_Indent
     (O    : in out Output_Record;
      Diff : Integer) is
   begin
      O.Indent := Natural (O.Indent + Diff);
   end Relative_Indent;

   ---------------------
   -- Absolute_Indent --
   ---------------------

   procedure Absolute_Indent
     (O     : in out Output_Record;
      Level : Natural) is
   begin
      O.Indent := Level;
   end Absolute_Indent;

end Outputs;
