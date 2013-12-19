------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                  F L O W _ E R R O R _ M E S S A G E S                   --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                  Copyright (C) 2013, Altran UK Limited                   --
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
with Ada.Text_IO;    use Ada.Text_IO;

with GNAT.String_Split;
with GNAT.SHA1;

with Atree;          use Atree;
with Einfo;          use Einfo;
with Errout;         use Errout;
with Erroutc;        use Erroutc;
with Opt;            use Opt;
with Sem_Util;       use Sem_Util;
with Sinfo;          use Sinfo;
with Sinput;         use Sinput;
with Stringt;        use Stringt;
with String_Utils;   use String_Utils;
with VC_Kinds;

with Gnat2Why.Nodes; use Gnat2Why.Nodes;
with Gnat2Why_Args;  use Gnat2Why_Args;

package body Flow_Error_Messages is

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
     (Msg       : String;
      N         : Node_Id;
      F1        : Flow_Id;
      F2        : Flow_Id;
      Tag       : String;
      SRM_Ref   : String;
      Warning   : Boolean;
      Tracefile : out Unbounded_String;
      E         : Entity_Id)
     with Pre => Present (E);
   --  If Ide_Mode is set then we print a JSON message. Otherwise, we just
   --  print a regular message. It also generates a unique Tracefile name
   --  based on a SHA1 hash of the JSON_Msg and adds a JSON entry to the
   --  "basename.flow" file.

   ------------
   -- Escape --
   ------------

   function Escape (S : Unbounded_String) return Unbounded_String is
      R : Unbounded_String := Null_Unbounded_String;
   begin
      for Index in Positive range 1 .. Length (S) loop
         if Element (S, Index) in '%' | '$' | '{' | '*' | '&' |
           '#' | '}' | '@' | '^' | '>' |
           '!' | '?' | '<' | '`' | ''' | '\' | '|' | '~'
         then
            Append (R, "'");
         end if;

         Append (R, Element (S, Index));
      end loop;

      return R;
   end Escape;

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

   ------------------------------
   -- Print_JSON_Or_Normal_Msg --
   ------------------------------

   procedure Print_JSON_Or_Normal_Msg
     (Msg       : String;
      N         : Node_Id;
      F1        : Flow_Id;
      F2        : Flow_Id;
      Tag       : String;
      SRM_Ref   : String;
      Warning   : Boolean;
      Tracefile : out Unbounded_String;
      E         : Entity_Id)
   is
      M          : Unbounded_String;
      JSON_M     : Unbounded_String;
      C          : GNAT.SHA1.Context;
      Slc        : Source_Ptr;

      File       : constant String := File_Name (Sloc (N));
      Line       : constant String := Get_Logical_Line_Number_Img (Sloc (N));
      Col        : constant String :=
        Int_Image (Integer (Get_Column_Number (Sloc (N))));
      Suppr_Reason : String_Id := No_String;

      function Warning_Disabled_For_Entity return Boolean;
      --  Returns True if either of N, F1, F2 correspond to an entity that
      --  Has_Warnings_Off.

      function Json_Entry (Reason : String_Id) return Unbounded_String;
      --  Build the string which contains the JSON dictionary. The Reason
      --  argument has the following meaning: if it is absent (= No_String),
      --  the warning is not suppressed; if it is empty (=Null_String_Id)
      --  the warning is suppressed, but we don't have a reason; Otherwise,
      --  the String contains the reason for the suppression.
      --  For suppressed messages, the JSON record will contain the reason of
      --  the suppression, if available.

      function Json_Mapping (Name      : String;
                             Value     : String;
                             Quote_Val : Boolean := True;
                             Is_Last   : Boolean := False)
                             return Unbounded_String;
      --  Helper function to produce the string
      --     "name": "value",
      --  Where name and value are substituted by the relevant
      --  parameters.
      --
      --  If Is_Last is set, then the trailing comma is omitted.
      --
      --  If Quote_Val is not set, the quotes around value are omitted.

      ---------------------------------------
      -- Warning_Disabled_For_Local_Entity --
      ---------------------------------------

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

      function Json_Entry (Reason : String_Id) return Unbounded_String is
         JSON_M     : Unbounded_String;
         Escaped_M : Unbounded_String := Null_Unbounded_String;
         Ent_Dict : Unbounded_String := To_Unbounded_String ("{");
         Subs     : GNAT.String_Split.Slice_Set;
         use type GNAT.String_Split.Slice_Number;
      begin

         --  Append file, line and column

         JSON_M := To_Unbounded_String ("{");
         Append (JSON_M, Json_Mapping ("file", File));
         Append (JSON_M, Json_Mapping ("line", Line, Quote_Val => False));
         Append (JSON_M, Json_Mapping ("col", Col, Quote_Val => False));

         if Reason = No_String then

            --  Before appending the message we first escape any '"' that are
            --  in it. The script is in python so we use '\' to escape it.

            if Warning then
               Append (Escaped_M, "warning: ");
            end if;

            for Index in Positive range 1 .. Length (M) loop
               if Element (M, Index) = '"' then
                  Append (Escaped_M, '\');
               end if;
               Append (Escaped_M, Element (M, Index));
            end loop;
         else
            for Index in Int range 1 .. String_Length (Reason) loop
               if Character'Val (Get_String_Char (Reason, Index)) = '"' then
                  Append (Escaped_M, '\');
               end if;
               Append (Escaped_M,
                       Character'Val (Get_String_Char (Reason, Index)));
            end loop;
         end if;
         Append (JSON_M,
                 Json_Mapping ("message", To_String (Escaped_M)));

         --  Append rule and severity
         Append (JSON_M,
                 Json_Mapping
                   ("rule",
                    (if Reason /= No_String then "pragma_warning" else Tag)));

         Append (JSON_M,
                 Json_Mapping
                   ("severity",
                    (if Warning then "warning" else "error")));

         --  Append entity information
         --  Originally the entity info looks like "GP_Subp:foo.ads:12" so
         --  we split it up (using ':' as the separator).

         GNAT.String_Split.Create (S          => Subs,
                                   From       => Subp_Location (E),
                                   Separators => ":");
         pragma Assert (GNAT.String_Split.Slice_Count (Subs) >= 3);

         Append (Ent_Dict, Json_Mapping ("file",
                                         GNAT.String_Split.Slice (Subs, 2)));

         Append (Ent_Dict, Json_Mapping ("line",
                                         GNAT.String_Split.Slice (Subs, 3),
                                         Quote_Val => False));

         Append (Ent_Dict, Json_Mapping ("name",
                                         Subprogram_Full_Source_Name (E),
                                         Is_Last => True));

         Append (Ent_Dict, "}");

         Append (JSON_M,
                 Json_Mapping ("entity",
                               To_String (Ent_Dict),
                               Quote_Val => False,
                               Is_Last => Reason /= No_String));

         --  a suppressed warning never has a trace file

         if Reason = No_String then
            --  Create a SHA1 hash of the current JSON message and then set
            --  that as the name of the tracefile.

            GNAT.SHA1.Update (C, To_String (JSON_M));
            Tracefile := To_Unbounded_String (GNAT.SHA1.Digest (C) & ".trace");

            --  Append tracefile and end the dictionary
            Append (JSON_M, Json_Mapping ("tracefile", To_String (Tracefile),
                    Is_Last => True));
         end if;

         Append (JSON_M, "}");

         return JSON_M;
      end Json_Entry;

      ------------------
      -- Json_Mapping --
      ------------------

      function Json_Mapping (Name      : String;
                             Value     : String;
                             Quote_Val : Boolean := True;
                             Is_Last   : Boolean := False)
                             return Unbounded_String
      is
         S : Unbounded_String := Null_Unbounded_String;
      begin
         Append (S, '"');
         Append (S, Name);
         Append (S, '"');

         Append (S, ": ");

         if Quote_Val then
            Append (S, '"');
         end if;
         Append (S, Value);
         if Quote_Val then
            Append (S, '"');
         end if;

         if not Is_Last then
            Append (S, ", ");
         end if;

         return S;
      end Json_Mapping;

   begin
      --  Assemble message string

      M := To_Unbounded_String (Msg);
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
            Tmp  : Source_Ptr := Sloc (First_Node (N));
            File : Unbounded_String;
            Line : Physical_Line_Number;
         begin
            loop
               Tmp := Instantiation_Location (Tmp);
               exit when Tmp = No_Location;
               File := To_Unbounded_String (File_Name (Tmp));
               Line := Get_Physical_Line_Number (Tmp);
               Append (M, ", in instantiation at " &
                         To_String (File) & ":" & Int_Image (Integer (Line)));
            end loop;
         end;

      else
         Slc := Sloc (N);
      end if;

      --  If the current message is a warning, we check if the warning should
      --  be suppressed. Suppressed warnings will still be handled below.

      if Warning then
         Suppr_Reason := Warnings_Suppressed (Sloc (N));
         if Suppr_Reason = No_String then
            declare
               Temp : aliased String := To_String (M);
            begin
               Suppr_Reason :=
                 Warning_Specifically_Suppressed
                   (Sloc (N),
                    Temp'Unchecked_Access);
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
      --     * the Warning_Mode is Treat_As_Error.

      if not Warning or Opt.Warning_Mode = Treat_As_Error then
         Found_Flow_Error := True;
      end if;

      JSON_M := Json_Entry (Suppr_Reason);

      --  Append the JSON message to JSON_Msgs_List.
      JSON_Msgs_List.Append (JSON_M);

      if Suppr_Reason = No_String then
         if Ide_Mode then

            --  If Ide_Mode is set, then we print the JSON message

            Put_Line (To_String (JSON_M));

         else

            --  Otherwise we issue an error message

            M := Escape (M);
            Append (M, "!!");
            if Warning then
               Append (M, '?');
            end if;

            Error_Msg (To_String (M), Slc);

         end if;
      end if;
   end Print_JSON_Or_Normal_Msg;

   ---------------------------
   -- Create_Flow_Msgs_File --
   ---------------------------

   procedure Create_Flow_Msgs_File (GNAT_Root : Node_Id) is
      FD : Ada.Text_IO.File_Type;

      Flow_File_Name : constant String :=
        Ada.Directories.Compose
          (Name      => Spec_File_Name_Without_Suffix
                          (Enclosing_Comp_Unit_Node (GNAT_Root)),
           Extension => VC_Kinds.Flow_Suffix);
      --  Holds the name of the file that contains all emitted flow messages
   begin
      Ada.Text_IO.Create (FD, Ada.Text_IO.Out_File, Flow_File_Name);

      Ada.Text_IO.Put (FD, "[");
      Ada.Text_IO.New_Line (FD);

      --  Write all elements except for the last one
      while JSON_Msgs_List.Length > 1 loop
         Ada.Text_IO.Put (FD, To_String (JSON_Msgs_List.First_Element) & ",");
         Ada.Text_IO.New_Line (FD);
         JSON_Msgs_List.Delete_First;
      end loop;

      --  Write the last element
      if not JSON_Msgs_List.Is_Empty then
         Ada.Text_IO.Put (FD, To_String (JSON_Msgs_List.First_Element));
         Ada.Text_IO.New_Line (FD);
      end if;

      Ada.Text_IO.Put (FD, "]");

      Ada.Text_IO.Close (FD);
   end Create_Flow_Msgs_File;

   --------------------
   -- Error_Msg_Flow --
   --------------------

   procedure Error_Msg_Flow
     (FA        : Flow_Analysis_Graphs;
      Tracefile : out Unbounded_String;
      Msg       : String;
      N         : Node_Id;
      F1        : Flow_Id := Null_Flow_Id;
      F2        : Flow_Id := Null_Flow_Id;
      Tag       : String  := "";
      SRM_Ref   : String  := "";
      Warning   : Boolean := False)
   is
      E : Entity_Id;
   begin

      case FA.Kind is
         when E_Subprogram_Body | E_Package =>
            E := FA.Analyzed_Entity;
         when E_Package_Body =>
            E := Spec_Entity (FA.Analyzed_Entity);
      end case;

      Print_JSON_Or_Normal_Msg
        (Msg       => Msg,
         N         => N,
         F1        => F1,
         F2        => F2,
         Tag       => Tag,
         SRM_Ref   => SRM_Ref,
         Warning   => Warning,
         Tracefile => Tracefile,
         E         => E);

   end Error_Msg_Flow;

end Flow_Error_Messages;
