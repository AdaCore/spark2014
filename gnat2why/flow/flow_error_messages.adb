------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                  F L O W _ E R R O R _ M E S S A G E S                   --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                  Copyright (C) 2013-2014, Altran UK Limited              --
--                  Copyright (C) 2013-2014, AdaCore                        --
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
------------------------------------------------------------------------------

with Ada.Directories;
with Ada.Text_IO;       use Ada.Text_IO;

with GNATCOLL.JSON;

with Atree;             use Atree;
with Einfo;             use Einfo;
with Errout;            use Errout;
with Erroutc;           use Erroutc;
with Namet;             use Namet;
with Opt;               use Opt;
with Sem_Util;          use Sem_Util;
with Sinfo;             use Sinfo;
with Sinput;            use Sinput;
with Stringt;           use Stringt;
with String_Utils;      use String_Utils;
with VC_Kinds;

with Gnat2Why.Nodes;    use Gnat2Why.Nodes;
with Gnat2Why_Args;     use Gnat2Why_Args;

package body Flow_Error_Messages is

   type Msg_Kind is (Error_Kind, Warning_Kind, Info_Kind);
   --  describes the three kinds of messages issued by gnat2why

   function Msg_Kind_To_String (Kind : Msg_Kind) return String;
   --  transform the msg kind into a string, for the JSON output

   procedure  Create_JSON_File
     (GNAT_Root : Node_Id;
      List      : GNATCOLL.JSON.JSON_Array;
      Suffix    : String);
   --  Write the JSON list in argument to the file "unit.suffix"

   Flow_Msgs : GNATCOLL.JSON.JSON_Array;
   --  This will hold all of the emitted flow messages in JSON format

   Proof_Msgs : GNATCOLL.JSON.JSON_Array;

   use type Ada.Containers.Count_Type;
   use type Flow_Graphs.Vertex_Id;
   use type Flow_Id_Sets.Set;

   function Escape (S : Unbounded_String) return Unbounded_String
     with Post => Length (Escape'Result) >= Length (S);
   --  Escape any special characters used in the error message (for
   --  example transforms "=>" into "='>" as > is a special insertion
   --  character.

   function Substitute
     (S : Unbounded_String;
      F : Flow_Id) return Unbounded_String;
   --  Find the first '&' or '#' and substitute with the given flow
   --  id, with or without enclosing quotes respectively.

   procedure Print_JSON_Or_Normal_Msg
     (Msg         : String;
      N           : Node_Id;
      F1          : Flow_Id;
      F2          : Flow_Id;
      Tag         : String;
      SRM_Ref     : String;
      Kind        : Msg_Kind;
      Place_First : Boolean;
      Msg_List    : in out GNATCOLL.JSON.JSON_Array;
      Tracefile   : String;
      E           : Entity_Id)
     with Pre => Present (E);
   --  If Ide_Mode is set then we print a JSON message. Otherwise, we just
   --  print a regular message. It also generates a unique Tracefile name
   --  based on a SHA1 hash of the JSON_Msg and adds a JSON entry to the
   --  "basename.flow" file.

   File_Counter : Integer := 0;

   ---------------------------
   -- Create_Flow_Msgs_File --
   ---------------------------

   procedure Create_Flow_Msgs_File (GNAT_Root : Node_Id) is
   begin
      Create_JSON_File (GNAT_Root, Flow_Msgs, VC_Kinds.Flow_Suffix);
   end Create_Flow_Msgs_File;

   ----------------------
   -- Create_JSON_File --
   ----------------------

   procedure  Create_JSON_File
     (GNAT_Root : Node_Id;
      List      : GNATCOLL.JSON.JSON_Array;
      Suffix    : String)
   is
      FD : Ada.Text_IO.File_Type;
      File_Name : constant String :=
        Ada.Directories.Compose
          (Name      => Spec_File_Name_Without_Suffix
             (Enclosing_Comp_Unit_Node (GNAT_Root)),
           Extension => Suffix);
      Full : constant GNATCOLL.JSON.JSON_Value :=
        GNATCOLL.JSON.Create (List);
   begin
      Ada.Text_IO.Create (FD, Ada.Text_IO.Out_File, File_Name);
      Ada.Text_IO.Put (FD, GNATCOLL.JSON.Write (Full, Compact => False));
      Ada.Text_IO.Close (FD);
   end Create_JSON_File;

   ----------------------------
   -- Create_Proof_Msgs_File --
   ----------------------------

   procedure Create_Proof_Msgs_File (GNAT_Root : Node_Id) is
   begin
      Create_JSON_File (GNAT_Root, Proof_Msgs, VC_Kinds.Proof_Suffix);
   end Create_Proof_Msgs_File;

   --------------------
   -- Error_Msg_Flow --
   --------------------

   procedure Error_Msg_Flow
     (FA        : Flow_Analysis_Graphs;
      Msg       : String;
      N         : Node_Id;
      F1        : Flow_Id               := Null_Flow_Id;
      F2        : Flow_Id               := Null_Flow_Id;
      Tag       : String                := "";
      SRM_Ref   : String                := "";
      Tracefile : String                := "";
      Warning   : Boolean               := False;
      Vertex    : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex)
   is
      E   : Entity_Id;
      Img : constant String := Natural'Image
        (FA.CFG.Vertex_To_Natural (Vertex));
      Tmp : constant String := (if Gnat2Why_Args.Flow_Advanced_Debug and then
                                  Vertex /= Flow_Graphs.Null_Vertex
                                then Msg & " <" & Img (2 .. Img'Last) & ">"
                                else Msg);
   begin

      case FA.Kind is
         when E_Subprogram_Body | E_Package =>
            E := FA.Analyzed_Entity;
         when E_Package_Body =>
            E := Spec_Entity (FA.Analyzed_Entity);
      end case;

      Print_JSON_Or_Normal_Msg
        (Msg         => Tmp,
         N           => N,
         F1          => F1,
         F2          => F2,
         Tag         => Tag,
         SRM_Ref     => SRM_Ref,
         Kind        => (if Warning then Warning_Kind else Error_Kind),
         Msg_List    => Flow_Msgs,
         Tracefile   => Tracefile,
         Place_First => False,
         E           => E);

   end Error_Msg_Flow;

   ---------------------
   -- Error_Msg_Proof --
   ---------------------

   procedure Error_Msg_Proof
     (N           : Node_Id;
      Msg         : String;
      Is_Proved   : Boolean;
      Tag         : String;
      Tracefile   : String;
      E           : Entity_Id;
      Place_First : Boolean) is
   begin
      Print_JSON_Or_Normal_Msg
        (Msg         => Msg,
         N           => N,
         F1          => Null_Flow_Id,
         F2          => Null_Flow_Id,
         Tag         => Tag,
         Kind        => (if Is_Proved then Info_Kind else Warning_Kind),
         SRM_Ref     => "",
         Msg_List    => Proof_Msgs,
         Tracefile   => Tracefile,
         Place_First => Place_First,
         E           => E);
   end Error_Msg_Proof;

   ------------
   -- Escape --
   ------------

   function Escape (S : Unbounded_String) return Unbounded_String is
      R : Unbounded_String := Null_Unbounded_String;
   begin
      for Index in Positive range 1 .. Length (S) loop
         if Element (S, Index) in '%' | '$' | '{' | '*' | '&' |
           '#' | '}' | '@' | '^' | '>' |
           '!' | '?' | '<' | '`' | ''' | '\' | '|'
         then
            Append (R, "'");
         end if;

         Append (R, Element (S, Index));
      end loop;

      return R;
   end Escape;

   function Fresh_Trace_File return String is
      Result : constant String :=
        Unit_Name & "__flow__" & Int_Image (File_Counter) & ".trace";
   begin
      File_Counter := File_Counter + 1;
      return Result;
   end Fresh_Trace_File;
   ------------------------
   -- Msg_Kind_To_String --
   ------------------------

   function Msg_Kind_To_String (Kind : Msg_Kind) return String is
   begin
      case Kind is
         when Error_Kind =>
            return "error";
         when Warning_Kind =>
            return "warning";
         when Info_Kind =>
            return "info";
      end case;
   end Msg_Kind_To_String;

   ------------------------------
   -- Print_JSON_Or_Normal_Msg --
   ------------------------------

   procedure Print_JSON_Or_Normal_Msg
     (Msg         : String;
      N           : Node_Id;
      F1          : Flow_Id;
      F2          : Flow_Id;
      Tag         : String;
      SRM_Ref     : String;
      Kind        : Msg_Kind;
      Place_First : Boolean;
      Msg_List    : in out GNATCOLL.JSON.JSON_Array;
      Tracefile   : String;
      E           : Entity_Id)
   is

      use GNATCOLL.JSON;

      M          : Unbounded_String;
      JSON_V     : JSON_Value;
      Slc        : Source_Ptr;

      Suppr_Reason : String_Id := No_String;

      function Warning_Disabled_For_Entity return Boolean;
      --  Returns True if either of N, F1, F2 correspond to an entity that
      --  Has_Warnings_Off.

      function Json_Entry (Reason : String_Id) return JSON_Value;
      --  Build the JSON value for a message. The Reason
      --  argument has the following meaning: if it is absent (= No_String),
      --  the warning is not suppressed; if it is empty (=Null_String_Id)
      --  the warning is suppressed, but we don't have a reason; Otherwise,
      --  the String contains the reason for the suppression.
      --  For suppressed messages, the JSON record will contain the reason of
      --  the suppression, if available.

      ---------------------------------
      -- Warning_Disabled_For_Entity --
      ---------------------------------

      function Warning_Disabled_For_Entity return Boolean is

         function Is_Entity_And_Has_Warnings_Off (N : Node_Or_Entity_Id)
                                                  return Boolean
         is ((Is_Entity_Name (N) and then Has_Warnings_Off (Entity (N)))
             or else (Nkind (N) in N_Entity and then Has_Warnings_Off (N)));
         --  Returns True if N is an entity and Has_Warnings_Off (N)

      begin
         if Is_Entity_And_Has_Warnings_Off (N) then
            return True;
         end if;

         if Present (F1)
           and then F1.Kind in Direct_Mapping | Record_Field
           and then Is_Entity_And_Has_Warnings_Off (Get_Direct_Mapping_Id (F1))
         then
            return True;
         end if;

         if Present (F2)
           and then F2.Kind in Direct_Mapping | Record_Field
           and then Is_Entity_And_Has_Warnings_Off (Get_Direct_Mapping_Id (F2))
         then
            return True;
         end if;

         return False;
      end Warning_Disabled_For_Entity;

      ----------------
      -- Json_Entry --
      ----------------

      function Json_Entry (Reason : String_Id) return JSON_Value is
         Value    : JSON_Value;
         Prefix    : constant String :=
           (case Kind is
               when Warning_Kind => "warning: ",
               when Info_Kind | Error_Kind => "");
         File       : constant String := File_Name (Sloc (N));
         Line       : constant Integer :=
           Integer (Get_Logical_Line_Number (Sloc (N)));
         Col        : constant Integer :=
           Integer (Get_Column_Number (Sloc (N)));
      begin

         --  Append file, line and column

         Value := Create_Object;
         Set_Field (Value, "file", File);
         Set_Field (Value, "line", Line);
         Set_Field (Value, "col", Col);

         if Reason = No_String then
            Set_Field (Value, "message", Prefix & M);
         else
            declare
               Len           : constant Natural :=
                 Natural (String_Length (Reason));
               Reason_String : String (1 .. Len);
            begin
               String_To_Name_Buffer (Reason);
               Reason_String := Name_Buffer (1 .. Len);
               Set_Field (Value, "message", Reason_String);
            end;
         end if;

         Set_Field (Value, "rule",
                    (if Reason /= No_String then "pragma_warning" else Tag));

         Set_Field (Value, "severity", Msg_Kind_To_String (Kind));

            --  Append entity information

         declare
            Ent_Value : constant JSON_Value := Create_Object;
            Loc       : constant Source_Ptr := Translate_Location (Sloc (E));
         begin
            Set_Field (Ent_Value, "file", File_Name (Loc));
            Set_Field (Ent_Value, "line",
                       Integer (Get_Physical_Line_Number (Loc)));
            Set_Field (Ent_Value, "name", Subprogram_Full_Source_Name (E));
            Set_Field (Value, "entity", Ent_Value);
         end;

         if Tracefile /= "" then
            Set_Field (Value, "tracefile", Tracefile);
         end if;

         return Value;
      end Json_Entry;

   begin
      --  Assemble message string

      if Kind = Info_Kind then
         Append (M, "info: ");
      end if;

      Append (M, Msg);
      if Present (F1) then
         M := Substitute (M, F1);
      end if;
      if Present (F2) then
         M := Substitute (M, F2);
      end if;

      if SRM_Ref'Length > 0 then
         Append (M, " (SPARK RM ");
         Append (M, SRM_Ref);
         Append (M, ")");
      end if;

      if Instantiation_Location (Sloc (N)) /= No_Location then
         --  If we are dealing with an instantiation of a generic we change
         --  the message to point at the implementation of the generic and we
         --  mention where the generic is instantiated.
         Slc := Original_Location (Sloc (N));

         declare
            Tmp     : Source_Ptr := Sloc (First_Node (N));
            File    : Unbounded_String;
            Line    : Physical_Line_Number;
            Context : Unbounded_String;
         begin
            loop
               exit when Instantiation_Location (Tmp) = No_Location;

               --  This wording for messages related to instantiations and
               --  inlined calls is the same for flow and proof messages.
               --  If you change it here, also change it in gnat_loc.ml

               if Comes_From_Inlined_Body (Tmp) then
                  Context := To_Unbounded_String (", in call inlined at ");
               else
                  Context := To_Unbounded_String (", in instantiation at ");
               end if;

               Tmp := Instantiation_Location (Tmp);
               File := To_Unbounded_String (File_Name (Tmp));
               Line := Get_Physical_Line_Number (Tmp);
               Append (M, To_String (Context) &
                         To_String (File) & ":" & Int_Image (Integer (Line)));
            end loop;
         end;

      elsif Place_First then
         Slc := First_Sloc (N);
      else
         Slc := Sloc (N);
      end if;

      --  If the current message is a warning, we check if the warning should
      --  be suppressed. Suppressed warnings will still be handled below.

      if Kind = Warning_Kind then
         Suppr_Reason := Warnings_Suppressed (Sloc (N));

         if Suppr_Reason = No_String then
            declare
               Temp : aliased String := To_String (M);
            begin
               Suppr_Reason :=
                 Warning_Specifically_Suppressed (Loc => Sloc (N),
                                                  Msg => Temp'Unchecked_Access,
                                                  Tag => Tag);
            end;

            if Suppr_Reason = No_String
              and then Warning_Disabled_For_Entity
            then
               Suppr_Reason := Null_String_Id;
            end if;
         end if;
      end if;

      --  Signal we have found an error if:
      --     * we are not dealing with a warning or
      --     * the Warning_Mode is Treat_As_Error and the warning is not
      --       suppressed.

      if Kind = Error_Kind or else
        (Kind = Warning_Kind and then
         Opt.Warning_Mode = Treat_As_Error and then
         Suppr_Reason = No_String)
      then
         Found_Flow_Error := True;
      end if;

      JSON_V := Json_Entry (Suppr_Reason);
      Append (Msg_List, JSON_V);

      --  ??? remove this covert channel We use the fact that only proved
      --  messages are info messages to detect when we are about to issue
      --  a proof message
      --  if report mode is "fail", do not actually print the message

      if Kind = Info_Kind and then Report_Mode = GPR_Fail then
         return;
      end if;

      if Suppr_Reason = No_String then
         if Ide_Mode then

            --  If Ide_Mode is set, then we print the JSON message

            Put_Line (Write (JSON_V));

         else

            --  Otherwise we issue an error message

            M := Escape (M);
            Append (M, "!!");

            if Kind /= Error_Kind then
               Append (M, "?");
            end if;

            Error_Msg (To_String (M), Slc);

         end if;
      end if;
   end Print_JSON_Or_Normal_Msg;

   ----------------
   -- Substitute --
   ----------------

   function Substitute
     (S : Unbounded_String;
      F : Flow_Id) return Unbounded_String
   is
      R      : Unbounded_String := Null_Unbounded_String;
      Do_Sub : Boolean          := True;
      Quote  : Boolean;
   begin
      for Index in Positive range 1 .. Length (S) loop
         if Do_Sub and then Element (S, Index) in '&' | '#' then
            Quote := Element (S, Index) = '&';

            if Quote then
               Append (R, """");
            end if;

            case F.Kind is
               when Null_Value =>
                  raise Program_Error;

               when Synthetic_Null_Export =>
                  Append (R, "null");

               when Direct_Mapping | Record_Field =>
                  Append (R, Flow_Id_To_String (F));

                  case F.Bound.Kind is
                     when No_Bound =>
                        null;

                     when Some_Bound =>
                        Append (R, "'Some_Bound");
                        --  raise Program_Error;
                  end case;

               when Magic_String =>
                  --  ??? we may want to use __gnat_decode() here instead
                  if F.Name.all = "__HEAP" then
                     Append (R, "the heap");
                  else
                     declare
                        Index : Positive := 1;
                     begin
                        --  Replace __ with . in the magic string.
                        while Index <= F.Name.all'Length loop
                           case F.Name.all (Index) is
                              when '_' =>
                                 if Index < F.Name.all'Length and then
                                   F.Name.all (Index + 1) = '_'
                                 then
                                    Append (R, ".");
                                    Index := Index + 2;
                                 else
                                    Append (R, '_');
                                    Index := Index + 1;
                                 end if;

                              when others =>
                                 Append (R, F.Name.all (Index));
                                 Index := Index + 1;
                           end case;
                        end loop;
                     end;
                  end if;
            end case;

            if Quote then
               Append (R, """");
            end if;

            Do_Sub := False;

         else
            Append (R, Element (S, Index));
         end if;
      end loop;

      return R;
   end Substitute;

end Flow_Error_Messages;
