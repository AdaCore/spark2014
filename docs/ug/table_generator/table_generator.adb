------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                        T A B L E _ G E N E R A T O R                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2018-2019, AdaCore                     --
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

with Ada.Directories; use Ada.Directories;
with Ada.Text_IO;     use Ada.Text_IO;
with VC_Kinds;        use VC_Kinds;

procedure Table_Generator is

   Target_Dir   : constant String := Compose ("en", "source");
   Flow_Target  : constant String :=
     Compose (Target_Dir, "flow_checks_table.rst");
   Proof_Target : constant String :=
     Compose (Target_Dir, "proof_checks_table.rst");

   subtype Class_Tag is Character
   with Static_Predicate => Class_Tag in 'E' | 'C' | 'W';
   --  Class is either an Error, Check or Warning (and represented by the first
   --  letter).

   function CWE_Ref (Arg : String) return String;
   --  If the argument is non-empty, return a string which will show in ReST
   --  as:
   --  "<CWE number> <link to CWE number>"

   procedure Produce_Flow_Checks_Table;
   procedure Produce_Proof_Checks_Table;

   type Flow_Msg_Types is array (Valid_Flow_Tag_Kind) of Class_Tag;
   --  Mapping from Flow_Tag_Kind to error/check/warning

   Flow_Msg_Type : constant Flow_Msg_Types :=
     (Aliasing                                    => 'C',
      Call_In_Type_Invariant                      => 'C',
      Call_To_Current_Task                        => 'C',
      Concurrent_Access                           => 'C',
      Dead_Code                                   => 'W',
      Default_Initialization_Mismatch             => 'C',
      Depends_Missing                             => 'C',
      Depends_Missing_Clause                      => 'C',
      Depends_Null                                => 'C',
      Depends_Wrong                               => 'C',
      Export_Depends_On_Proof_In                  => 'C',
      Ghost_Wrong                                 => 'C',
      Global_Missing                              => 'E',
      Global_Wrong                                => 'C',
      Hidden_Unexposed_State                      => 'C',
      Illegal_Update                              => 'C',
      Impossible_To_Initialize_State              => 'C',
      Ineffective                                 => 'W',
      Initializes_Wrong                           => 'C',
      Inout_Only_Read                             => 'C',
      Missing_Return                              => 'C',
      Non_Volatile_Function_With_Volatile_Effects => 'C',
      Not_Constant_After_Elaboration              => 'C',
      Pragma_Elaborate_All_Needed                 => 'C',
      Pragma_Elaborate_Body_Needed                => 'C',
      Potentially_Blocking_In_Protected           => 'C',
      Reference_To_Non_CAE_Variable               => 'C',
      Refined_State_Wrong                         => 'C',
      Side_Effects                                => 'E',
      Stable                                      => 'W',
      Subprogram_Termination                      => 'C',
      Uninitialized                               => 'C',
      Unused                                      => 'W',
      Unused_Initial_Value                        => 'W',
      Volatile_Function_Without_Volatile_Effects  => 'C'
     );
   --  ??? some tags are used for both checks and warnings

   -------------
   -- CWE_Ref --
   -------------

   function CWE_Ref (Arg : String) return String is
   begin
      if Arg = "" then
         return "";
      else
         return "CWE `" & Arg & " <http://cwe.mitre.org/data/definitions/" &
           Arg & ".html>`_";
      end if;
   end CWE_Ref;

   -------------------------------
   -- Produce_Flow_Checks_Table --
   -------------------------------

   procedure Produce_Flow_Checks_Table is
      File : File_Type;
   begin
      Create (File, Name => Flow_Target);
      Put_Line (File, "Messages reported by Flow Analysis");
      Put_Line (File, "----------------------------------");
      New_Line (File);
      Put_Line (File, "The following table shows all flow analysis " &
                  "messages, (E)rrors, (W)arnings and (C)hecks.");
      New_Line (File);
      Put_Line (File, ".. tabularcolumns:: |p{3in}|l|l|p{3in}|");
      New_Line (File);
      Put_Line (File, ".. csv-table::");
      Put_Line (File, "   :header: ""Message Kind"", ""Class"", ""CWE"", " &
                  """Explanation""");
      Put_Line (File, "   :widths: 1, 1, 1, 6");
      New_Line (File);
      for Kind in Valid_Flow_Tag_Kind loop
         Put (File, "    ");
         Put (File, """" & Kind_Name (Kind) & """, ");
         Put (File, """" & Flow_Msg_Type (Kind) & """, ");
         Put (File, """" & CWE_Ref (CWE_ID (Kind)) & """, ");
         Put (File, """" & Description (Kind) & """");
         New_Line (File);
      end loop;
      New_Line (File);
      Put_Line (File, ".. note::");
      Put_Line (File, "    Certain messages emitted by flow analysis are " &
                  "classified as errors and consequently cannot be " &
                  "suppressed or justified.");
   end Produce_Flow_Checks_Table;

   --------------------------------
   -- Produce_Proof_Checks_Table --
   --------------------------------

   procedure Produce_Proof_Checks_Table is
      File : File_Type;

      procedure Put_Check_Line (Kind : VC_Kind);

      --------------------
      -- Put_Check_Line --
      --------------------

      procedure Put_Check_Line (Kind : VC_Kind) is
      begin
         Put (File, "   ");
         Put (File, """" & Kind_Name (Kind) & """, ");
         declare
            Ref : String renames  CWE_Ref (CWE_ID (Kind));
         begin
            if Ref /= "" then
               Put (File, """" & Ref & """, ");
            else
               Put (File, ",");
            end if;
         end;
         Put (File, """" & Description (Kind) & """");
         New_Line (File);
      end Put_Check_Line;

   begin
      Create (File, Name => Proof_Target);
      Put_Line (File, "Messages reported by Proof");
      Put_Line (File, "--------------------------");
      New_Line (File);
      Put_Line (File, ".. tabularcolumns:: |l|l|p{3in}|");
      New_Line (File);
      Put_Line (File, ".. csv-table::");
      Put_Line (File, "   :header: ""Message Kind"", ""CWE"", " &
                  """Explanation""");
      Put_Line (File, "   :widths: 1, 1, 4");
      New_Line (File);
      Put_Line (File, "   **run-time checks**");
      for Kind in VC_RTE_Kind loop
         Put_Check_Line (Kind);
      end loop;
      New_Line (File);
      Put_Line (File, "   **assertions**");
      for Kind in VC_Assert_Kind loop
         Put_Check_Line (Kind);
      end loop;
      New_Line (File);
      Put_Line (File, "   **Liskov Substitution Principle**");
      for Kind in VC_LSP_Kind loop
         Put_Check_Line (Kind);
      end loop;
   end Produce_Proof_Checks_Table;

   --  Start of processing for Table_Generator

begin
   Produce_Flow_Checks_Table;
   Produce_Proof_Checks_Table;
end Table_Generator;
