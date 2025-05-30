------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                        T A B L E _ G E N E R A T O R                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2018-2022, AdaCore                     --
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

   Target_Dir                     : constant String :=
     Compose ("en", "source");
   Flow_Target                    : constant String :=
     Compose (Target_Dir, "flow_checks_table.rst");
   Proof_Target                   : constant String :=
     Compose (Target_Dir, "proof_checks_table.rst");
   Warnings_Target                : constant String :=
     Compose (Target_Dir, "misc_warnings_table.rst");
   Tool_Limitations_Target        : constant String :=
     Compose (Target_Dir, "unsupported_constructs.rst");
   Other_Tool_Limitations_Target  : constant String :=
     Compose (Target_Dir, "other_tool_limitations.rst");
   Flow_Limitations_Target        : constant String :=
     Compose (Target_Dir, "flow_limitations.rst");
   Proof_Limitations_Target       : constant String :=
     Compose (Target_Dir, "proof_limitations.rst");

   subtype Class_Tag is Character
   with Static_Predicate => Class_Tag in 'E' | 'C' | 'W';
   --  Class is either an Error, Check or Warning (and represented by the first
   --  letter).

   function CWE_Ref (Arg : String) return String;
   --  If the argument is non-empty, return a string which will show in ReST
   --  as:
   --  "<CWE number> <link to CWE number>"

   procedure Produce_Flow_Checks_Table;
   procedure Produce_Tool_Limitation_List;
   procedure Produce_Other_Tool_Limitation_List;
   procedure Produce_Flow_Limitation_List;
   procedure Produce_Proof_Limitation_List;
   procedure Produce_Proof_Checks_Table;
   procedure Produce_Misc_Warnings_Table;

   function Flow_Msg_Type (Tag : Valid_Flow_Tag_Kind) return Class_Tag is
     (case Tag is
        when Flow_Error_Kind   => 'E',
        when Flow_Check_Kind   => 'C',
        when Flow_Warning_Kind => 'W');

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
      Put_Line (File, ".. tabularcolumns:: |p{2in}|l|l|p{3in}|");
      New_Line (File);
      Put_Line (File, ".. csv-table::");
      Put_Line (File, "   :header: ""Message Tag"", ""Class"", ""CWE"", " &
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

   ----------------------------------
   -- Produce_Flow_Limitation_List --
   ----------------------------------

   procedure Produce_Flow_Limitation_List is
      File : File_Type;
   begin
      Create (File, Name => Flow_Limitations_Target);
      Put_Line (File, "The following constructs are imprecisely supported in" &
                  " flow analysis. They can be used safely but might lead to" &
                  " unprovable checks. Warnings can be emitted by GNATprove" &
                  " if the ``--info`` switch is used:");
      New_Line (File);
      for Kind in Flow_Limitation_Kind loop
         Put (File, "* ");
         Put (File, Description (Kind));
         if Kind = Flow_Limitation_Kind'Last then
            Put_Line (File, ".");
         else
            Put_Line (File, ",");
         end if;
         New_Line (File);
      end loop;
   end Produce_Flow_Limitation_List;

   ---------------------------------
   -- Produce_Misc_Warnings_Table --
   ---------------------------------

   procedure Produce_Misc_Warnings_Table is
      File : File_Type;
   begin
      Create (File, Name => Warnings_Target);
      Put_Line (File, "Miscellaneous warnings reported by GNATprove");
      Put_Line (File, "--------------------------------------------");
      New_Line (File);
      Put_Line (File, "The following table shows default warnings " &
                  "reported by GNATprove outside of flow analysis and proof.");
      New_Line (File);
      Put_Line (File, ".. tabularcolumns:: |p{2in}|p{3in}|");
      New_Line (File);
      Put_Line (File, ".. csv-table::");
      Put_Line (File, "   :header: ""Warning Tag"", ""Explanation""");
      Put_Line (File, "   :widths: 2, 4");
      New_Line (File);
      for Kind in Default_Warning_Kind loop
         Put (File, "    ");
         Put (File, """" & Kind_Name (Kind) & """, ");
         Put (File, """" & Description (Kind) & """");
         New_Line (File);
      end loop;
      New_Line (File);
      Put_Line (File, "The following table shows warnings " &
                  "guaranteed to be reported by GNATprove.");
      New_Line (File);
      Put_Line (File, ".. tabularcolumns:: |p{2in}|p{3in}|");
      New_Line (File);
      Put_Line (File, ".. csv-table::");
      Put_Line (File, "   :header: ""Warning Tag"", ""Explanation""");
      Put_Line (File, "   :widths: 2, 4");
      New_Line (File);
      for Kind in Guaranteed_Warning_Kind loop
         Put (File, "    ");
         Put (File, """" & Kind_Name (Kind) & """, ");
         Put (File, """" & Description (Kind) & """");
         New_Line (File);
      end loop;
      New_Line (File);
      Put_Line (File, "The following warnings are disabled by default, and " &
                  "can be enabled collectively using switch ``--pedantic``, "
                & " or individually using switch ``-W``.");
      New_Line (File);
      Put_Line (File, ".. tabularcolumns:: |p{2in}|p{3in}|");
      New_Line (File);
      Put_Line (File, ".. csv-table::");
      Put_Line (File, "   :header: ""Warning Tag"", ""Explanation""");
      Put_Line (File, "   :widths: 2, 4");
      New_Line (File);
      for Kind in Pedantic_Warning_Kind loop
         Put (File, "    ");
         Put (File, """" & Kind_Name (Kind) & """, ");
         Put (File, """" & Description (Kind) & """");
         New_Line (File);
      end loop;
      New_Line (File);
      Put_Line (File, "The following warnings are disabled by default, and " &
                  "can be enabled collectively using switch ``--info``, "
                & " or individually using switch ``-W``.");
      New_Line (File);
      Put_Line (File, ".. tabularcolumns:: |p{2in}|p{3in}|");
      New_Line (File);
      Put_Line (File, ".. csv-table::");
      Put_Line (File, "   :header: ""Warning Tag"", ""Explanation""");
      Put_Line (File, "   :widths: 2, 4");
      New_Line (File);
      for Kind in Info_Warning_Kind loop
         Put (File, "    ");
         Put (File, """" & Kind_Name (Kind) & """, ");
         Put (File, """" & Description (Kind) & """");
         New_Line (File);
      end loop;
      New_Line (File);
      Put_Line (File, "The following info messages are issued by default, and "
                &  "can be disabled using switch ``-A``.");
      New_Line (File);
      Put_Line (File, ".. tabularcolumns:: |p{2in}|p{3in}|");
      New_Line (File);
      Put_Line (File, ".. csv-table::");
      Put_Line (File, "   :header: ""Warning Tag"", ""Explanation""");
      Put_Line (File, "   :widths: 2, 4");
      New_Line (File);
      for Kind in Info_Msg_Kind loop
         Put (File, "    ");
         Put (File, """" & Kind_Name (Kind) & """, ");
         Put (File, """" & Description (Kind) & """");
         New_Line (File);
      end loop;
   end Produce_Misc_Warnings_Table;

   ----------------------------------------
   -- Produce_Other_Tool_Limitation_List --
   ----------------------------------------

   procedure Produce_Other_Tool_Limitation_List is
      File : File_Type;
   begin
      Create (File, Name => Other_Tool_Limitations_Target);
      Put_Line (File, "The following constructs are incompletely supported." &
                  " They can be used safely but might lead to unexpected " &
                  "behavior. Warnings for these constructs can be enabled " &
                  "individually using the ``-W`` switch and the tag " &
                  "between parentheses, or collectively using the " &
                  "``--info`` switch.");
      New_Line (File);
      for Kind in Other_Tool_Limitation_Kind loop
         Put (File, "* ");
         Put (File, Description (Kind));
         Put (File, " (" & Kind_Name (Kind) & ")");
         if Kind = Other_Tool_Limitation_Kind'Last then
            Put_Line (File, ".");
         else
            Put_Line (File, ",");
         end if;
         New_Line (File);
      end loop;
   end Produce_Other_Tool_Limitation_List;

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
            Ref : String renames CWE_Ref (CWE_ID (Kind));
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
      Put_Line (File, "The following table shows all check " &
                  "messages reported by proof.");
      New_Line (File);
      Put_Line (File, ".. tabularcolumns:: |p{2in}|l|p{3in}|");
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
      New_Line (File);
      Put_Line (File, "The following table shows all warning " &
                  "messages reported by proof when using switch " &
                  "``--proof-warnings=on``.");
      New_Line (File);
      Put_Line (File, ".. tabularcolumns:: |p{2in}|l|p{3in}|");
      New_Line (File);
      Put_Line (File, ".. csv-table::");
      Put_Line (File, "   :header: ""Warning Tag"", ""CWE"", " &
                  """Explanation""");
      Put_Line (File, "   :widths: 1, 1, 4");
      New_Line (File);
      for Kind in VC_Warning_Kind loop
         Put_Check_Line (Kind);
      end loop;
   end Produce_Proof_Checks_Table;

   -----------------------------------
   -- Produce_Proof_Limitation_List --
   -----------------------------------

   procedure Produce_Proof_Limitation_List is
      File : File_Type;
   begin
      Create (File, Name => Proof_Limitations_Target);
      Put_Line (File, "The following constructs are imprecisely supported " &
                  "in proof. They can be used safely but might lead to " &
                  "unexpected behavior. Warnings for these constructs can " &
                  " be enabled individually using the ``-W`` switch and the " &
                  "tag between parentheses, or collectively using the " &
                  "``--info`` switch.");
      New_Line (File);
      for Kind in Proof_Limitation_Kind loop
         Put (File, "* ");
         Put (File, Description (Kind));
         Put (File, " (" & Kind_Name (Kind) & ")");
         if Kind = Proof_Limitation_Kind'Last then
            Put_Line (File, ".");
         else
            Put_Line (File, ",");
         end if;
         New_Line (File);
      end loop;
   end Produce_Proof_Limitation_List;

   ----------------------------------
   -- Produce_Tool_Limitation_List --
   ----------------------------------

   procedure Produce_Tool_Limitation_List is
      File : File_Type;
   begin
      Create (File, Name => Tool_Limitations_Target);
      Put_Line (File, "The following unsupported constructs " &
                  "are detected by GNATprove and reported through an error " &
                  "message:");
      New_Line (File);
      for Kind in Unsupported_Kind loop
         Put (File, "* ");
         Put (File, Description (Kind));
         if Kind = Unsupported_Kind'Last then
            Put_Line (File, ".");
         else
            Put_Line (File, ",");
         end if;
         New_Line (File);
      end loop;
   end Produce_Tool_Limitation_List;

   --  Start of processing for Table_Generator

begin
   Produce_Flow_Checks_Table;
   Produce_Proof_Checks_Table;
   Produce_Misc_Warnings_Table;
   Produce_Tool_Limitation_List;
   Produce_Other_Tool_Limitation_List;
   Produce_Flow_Limitation_List;
   Produce_Proof_Limitation_List;
end Table_Generator;
