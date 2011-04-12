------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                              A L T E R G O                               --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or modify it  --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnatprove is distributed in the hope that it will  be  useful,  --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Directories;
with Ada.IO_Exceptions;
with Ada.Strings;
with Ada.Strings.Fixed; use Ada.Strings.Fixed;
with Ada.Strings.Maps;
with Ada.Text_IO;

with GNAT.Directory_Operations.Iteration;
with GNAT.Expect;       use GNAT.Expect;

package body Altergo is

   Main_Suffix  : constant String := "__package";

   type Explanation is
      record
         EX_Filename : String_Access;
         EX_Line     : String_Access;
         EX_Col      : String_Access;
         EX_Kind     : String_Access;
      end record;

   function Get_VC_Explanation (Expl_File : String) return Explanation;
   --  Parse an explanation file to return an explanation record

   function Call_AltErgo_On_File
     (File        : String;
      Result_File : String;
      Timeout     : Natural;
      Verbose     : Boolean := False) return Boolean;
   --  Call Altergo on a single File. Produce a file containing the result of
   --  the run with name Result_File. Don't take more time than the given
   --  Timeout in seconds. If the return value is "True", the VC has been
   --  proven, otherwise some error (timeout etc) was detected.

   procedure Cat
      (Files   : Argument_List;
       Target  : String;
       Success : out Boolean;
       Verbose : Boolean := False);
   --  Cat all the Files together into the Target.

   procedure Print_Error_Msg (X : Explanation; Proved : Boolean := False);
   --  Print an error message corresponding to the explanation in argument.

   function Starts_With (S, Prefix : String) return Boolean;
   --  Check if S starts with Prefix

   ------------------
   -- Call_Altergo --
   ------------------

   procedure Call_Altergo
      (Proj : Project_Tree;
       File : Virtual_File;
       Verbose : Boolean := False;
       Report  : Boolean := False) is
      pragma Unreferenced (Proj);

      Base : constant String := Ada.Directories.Base_Name (+Base_Name (File));

      procedure Call_AltErgo_On_Vc
        (Item  : String;
         Index : Positive;
         Quit : in out Boolean);
      --  Call Altergo on the VC that corresponds to the file
      --  'Item'; take into account the context file.

      ------------------------
      -- Call_AltErgo_On_Vc --
      ------------------------

      procedure Call_AltErgo_On_Vc
        (Item    : String;
         Index   : Positive;
         Quit    : in out Boolean)
      is
         pragma Unreferenced (Index);
         Target : constant String := "new.why";
         Success : aliased Boolean;
         Base_Of_VC : constant String :=
            Ada.Directories.Base_Name (Item);
         Proved : Boolean := False;
      begin
         Delete_File (Target, Success);
         Cat (Files =>
               (1 => new String'(Base & Main_Suffix & "_ctx.why"),
                2 => new String'(Item)),
              Target => Target,
              Success => Success,
              Verbose => Verbose);
         --  ??? use 10 as timeout for now
         Proved :=
           Call_AltErgo_On_File (Target, Base_Of_VC & ".rgo", 10, Verbose);
         if not Proved or else Report then
            Print_Error_Msg (Get_VC_Explanation (Base_Of_VC & ".xpl"), Proved);
         end if;
         Quit := not Success;
         Delete_File (Target, Success);
      end Call_AltErgo_On_Vc;

      procedure Iterate is new
         GNAT.Directory_Operations.Iteration.Wildcard_Iterator
           (Action => Call_AltErgo_On_Vc);

      --  beginning of processing for Call_Altergo

   begin
      Iterate (Path => Base & Main_Suffix & "_po*.why");
   end Call_Altergo;

   --------------------------
   -- Call_AltErgo_On_File --
   --------------------------

   function Call_AltErgo_On_File
     (File        : String;
      Result_File : String;
      Timeout     : Natural;
      Verbose     : Boolean := False
      ) return Boolean is
   begin
      if Verbose then
         Ada.Text_IO.Put_Line ("calling Alt-ergo on " & File);
      end if;

      declare
         Status  : aliased Integer;
         S       : constant String :=
            GNAT.Expect.Get_Command_Output
              (Command   => "why-cpulimit",
               Arguments =>
                 ((1 => new String'(Natural'Image (Timeout)),
                   2 => new String'("alt-ergo"),
                   3 => new String'(File))),
               Input     => "",
               Status    => Status'Access,
               Err_To_Out => True);
         FT      : Ada.Text_IO.File_Type;
         Success : Boolean;

      begin
         Ada.Text_IO.Create (FT, Ada.Text_IO.Out_File, Result_File);

         if Status /= 0 or else S'Length = 0 then
            Ada.Text_IO.Put (FT, "File """);
            Ada.Text_IO.Put (FT, File);
            Ada.Text_IO.Put_Line (FT, """:Failure or Timeout");
            Success := False;
         else
            Ada.Text_IO.Put (FT, S);
            Success := Ada.Strings.Fixed.Index (S, "Valid") > 0;
         end if;
         Ada.Text_IO.Close (FT);
         return Success;
      end;
   end Call_AltErgo_On_File;

   --------------------------
   -- Call_Exit_On_Failure --
   --------------------------

   procedure Call_Exit_On_Failure
     (Command   : String;
      Arguments : Argument_List;
      Verbose   : Boolean := False)
   is
      Status : aliased Integer;

      procedure Print_Command_Line;
      --  print the command line for debug purposes

      ------------------------
      -- Print_Command_Line --
      ------------------------

      procedure Print_Command_Line is
      begin
         Ada.Text_IO.Put (Command);

         for Index in Arguments'Range loop
            declare
               S : constant String_Access := Arguments (Index);
            begin
               Ada.Text_IO.Put (" ");
               Ada.Text_IO.Put (S.all);
            end;
         end loop;
      end Print_Command_Line;

   begin
      if Verbose then
         Print_Command_Line;
         Ada.Text_IO.Put_Line ("");
      end if;

      declare
         S : constant String :=
            GNAT.Expect.Get_Command_Output
              (Command   => Command,
               Arguments => Arguments,
               Input     => "",
               Status    => Status'Access,
               Err_To_Out => True);
      begin
         if Status /= 0 then
            Print_Command_Line;
            Ada.Text_IO.Put_Line (" failed.");
            Ada.Text_IO.Put (S);
            GNAT.OS_Lib.OS_Exit (1);
         end if;

         for Index in Arguments'Range loop
            declare
               S : String_Access := Arguments (Index);
            begin
               Free (S);
            end;
         end loop;
      end;
   end Call_Exit_On_Failure;

   ---------
   -- Cat --
   ---------

   procedure Cat
     (Files   : Argument_List;
      Target  : String;
      Success : out Boolean;
      Verbose : Boolean := False) is
   begin
      if Verbose then
         Ada.Text_IO.Put ("cat ");

         for Index in Files'Range loop
            Ada.Text_IO.Put (Files (Index).all);
            Ada.Text_IO.Put (" ");
         end loop;

         Ada.Text_IO.Put ("> ");
         Ada.Text_IO.Put_Line (Target);
      end if;

      for Index in Files'Range loop
         Copy_File
           (Name     => Files (Index).all,
            Pathname => Target,
            Success  => Success,
            Mode     => Append,
            Preserve => None);
         exit when not Success;
      end loop;
   end Cat;

   ------------------------
   -- Get_VC_Explanation --
   ------------------------

   function Get_VC_Explanation (Expl_File : String) return Explanation
   is
      use Ada.Text_IO;
      File : File_Type;
      Expl : Explanation;

      Char_Set : constant Ada.Strings.Maps.Character_Set :=
         Ada.Strings.Maps.To_Set (""" \n");
   begin
      Open (File, In_File, Expl_File);
      while True loop
         declare
            S : constant String := Get_Line (File);
         begin
            if Starts_With (S, "file") then
               Expl.EX_Filename :=
                  new String'(Trim (S (7 .. S'Last), Char_Set, Char_Set));
            elsif Starts_With (S, "line") then
               Expl.EX_Line :=
                  new String'(Trim (S (7 .. S'Last), Char_Set, Char_Set));
            elsif Starts_With (S, "kind") then
               Expl.EX_Kind :=
                  new String'(Trim (S (7 .. S'Last), Char_Set, Char_Set));
            elsif Starts_With (S, "begin") then
               Expl.EX_Col :=
                  new String'(Trim (S (8 .. S'Last), Char_Set, Char_Set));
            end if;
         end;
      end loop;
      return Expl;
   exception
      when Ada.IO_Exceptions.End_Error =>
         return Expl;
   end Get_VC_Explanation;

   ---------------------
   -- Print_Error_Msg --
   ---------------------

   procedure Print_Error_Msg (X : Explanation; Proved : Boolean := False) is
      use Ada.Text_IO;
   begin
      Put (X.EX_Filename.all);
      Put (":");
      Put (X.EX_Line.all);
      Put (":");
      Put (X.EX_Col.all);
      Put (":");
      if Proved then
         Put (" Proved - ");
      else
         Put (" ");
      end if;
      Put_Line (X.EX_Kind.all);
   end Print_Error_Msg;

   -----------------
   -- Starts_With --
   -----------------

   function Starts_With (S, Prefix : String) return Boolean is
   begin
      if S'Length < Prefix'Length then
         return False;
      end if;
      for Index in Prefix'Range loop
         if S (S'First + Index - Prefix'First) /= Prefix (Index) then
            return False;
         end if;
      end loop;
      return True;
   end Starts_With;

end Altergo;
