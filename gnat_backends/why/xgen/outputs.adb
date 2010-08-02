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

with Ada.Wide_Text_IO; use Ada.Wide_Text_IO;

package body Outputs is

   procedure I  (O : in out Output_Record);

   -------
   -- I --
   -------

   procedure I (O : in out Output_Record) is
   begin
      if O.New_Line then
         for J in 1 .. O.Indent loop
            Put (" ");
         end loop;
         O.New_Line := False;
      end if;
   end I;

   -------------------
   -- Library_Level --
   -------------------

   procedure Library_Level (O : in out Output_Record) is
   begin
      O.Indent := 3;
      O.New_Line := True;
   end Library_Level;

   --------
   -- NL --
   --------

   procedure NL (O : in out Output_Record) is
   begin
      New_Line;
      O.New_Line := True;
   end NL;

   -----------------
   -- Open_Output --
   -----------------

   function Open_Output return Output_Record is
   begin
      return Output_Record'(0, False);
   end Open_Output;

   -------
   -- P --
   -------

   procedure P  (O : in out Output_Record; S : Wide_String) is
   begin
      I (O);
      Put (S);
   end P;

   --------
   -- PL --
   --------

   procedure PL (O : in out Output_Record; S : Wide_String) is
   begin
      I (O);
      Put_Line (S);
      O.New_Line := True;
   end PL;

   ---------------------
   -- Relative_Indent --
   ---------------------

   procedure Relative_Indent (O : in out Output_Record; Diff : Integer) is
   begin
      O.Indent := Natural (O.Indent + Diff);
   end Relative_Indent;

end Outputs;
