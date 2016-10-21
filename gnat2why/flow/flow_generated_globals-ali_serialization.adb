------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--  F L O W . G E N E R A T E D _ G L O B A L S . S E R I A L I Z A T I O N --
--                                                                          --
--                                B o d y                                   --
--                                                                          --
--                  Copyright (C) 2016, Altran UK Limited                   --
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

with Ada.Strings.Unbounded;   use Ada.Strings.Unbounded;
with SPARK_Frame_Conditions;  use SPARK_Frame_Conditions;

package body Flow_Generated_Globals.ALI_Serialization is

   Invalid_Entity_Name : constant Entity_Name := Entity_Name'Last;
   --  Special dummy value for serialization which is not expected to represent
   --  any valid entity name, yet it must reside in the Entity_Name type.

   Null_Global_Info : constant Global_Phase_1_Info :=
     (Name   => Invalid_Entity_Name,
      Kind   => Analyzed_Subject_Kind'First,
      Origin => Globals_Origin_T'First,
      others => <>);
   --  Dummy value required only for the serialization API

   Null_ALI_Entry : constant array (ALI_Entry_Kind) of ALI_Entry :=
     (EK_Error              => (Kind => EK_Error),

      EK_End_Marker         => (Kind => EK_End_Marker),

      EK_State_Map          => (Kind      => EK_State_Map,
                                The_State => Invalid_Entity_Name,
                                others    => <>),

      EK_Remote_States      => (Kind          => EK_Remote_States,
                                The_Remote_States => Name_Sets.Empty_Set),

      EK_Volatiles          => (Kind   => EK_Volatiles,
                                others => <>),

      EK_Globals            => (Kind            => EK_Globals,
                                The_Global_Info => Null_Global_Info),

      EK_Protected_Instance => (Kind         => EK_Protected_Instance,
                                The_Variable => Invalid_Entity_Name,
                                The_Priority => Priority_Value'
                                  (Kind  => Priority_Kind'First,
                                   Value => 0)),

      EK_Task_Instance      => (Kind       => EK_Task_Instance,
                                The_Type   => Invalid_Entity_Name,
                                The_Object => Task_Object'
                                  (Name      => Invalid_Entity_Name,
                                   Instances => Instance_Number'First,
                                   Node      => Empty)),

      EK_Tasking_Info       => (Kind       => EK_Tasking_Info,
                                The_Entity => Invalid_Entity_Name,
                                others     => <>),

      EK_Nonblocking        => (Kind   => EK_Nonblocking,
                                others => <>),

      EK_Nonreturning       => (Kind   => EK_Nonreturning,
                                others => <>),

      EK_Direct_Calls       => (Kind       => EK_Direct_Calls,
                                The_Caller => Invalid_Entity_Name,
                                others     => <>)
     );
   --  Dummy value required only for the serialization API

   procedure Serialize (A : in out Archive; V : in out Entity_Name);

   procedure Serialize is new Serialize_Set
     (T                => Name_Sets.Set,
      E                => Entity_Name,
      Cursor           => Name_Sets.Cursor,
      Null_Container   => Name_Sets.Empty_Set,
      Null_Element     => Invalid_Entity_Name,
      First            => Name_Sets.First,
      Next             => Name_Sets.Next,
      Length           => Name_Sets.Length,
      Reserve_Capacity => Name_Sets.Reserve_Capacity,
      Element          => Name_Sets.Element,
      Insert           => Name_Sets.Insert);

   procedure Serialize (A : in out Archive; V : in out Task_Object);

   procedure Serialize (A : in out Archive; V : in out Name_Tasking_Info);

   procedure Serialize (A : in out Archive; V : in out Global_Phase_1_Info);

   ---------------
   -- Serialize --
   ---------------

   procedure Serialize (A : in out Archive; V : in out Entity_Name) is
      S : Unbounded_String;
   begin
      if A.Kind = Serialisation.Output then
         S := To_Unbounded_String (To_String (V));
      end if;
      Serialize (A, S);
      if A.Kind = Serialisation.Input then
         V := To_Entity_Name (To_String (S));
      end if;
   end Serialize;

   procedure Serialize (A : in out Archive; V : in out Task_Object) is
      procedure Serialize is new Serialisation.Serialize_Discrete
        (T => Instance_Number);
   begin
      Serialize (A, V.Name);
      Serialize (A, V.Instances);
      --  ??? Serialize (A, V.Node);
      if A.Kind = Serialisation.Input then
         V.Node := Find_Entity (V.Name);
      end if;
   end Serialize;

   procedure Serialize (A : in out Archive; V : in out Name_Tasking_Info) is
   begin
      for Kind in Tasking_Info_Kind loop
         Serialize (A, V (Kind), Kind'Img);
      end loop;
   end Serialize;

   procedure Serialize (A : in out Archive; V : in out Global_Phase_1_Info) is
      procedure Serialize is new Serialisation.Serialize_Discrete
        (T => Analyzed_Subject_Kind);
      procedure Serialize is new Serialisation.Serialize_Discrete
        (T => Globals_Origin_T);

   begin
      Serialize (A, V.Name);
      Serialize (A, V.Kind);
      Serialize (A, V.Origin);
      Serialize (A, V.Inputs_Proof,          "var_proof");
      Serialize (A, V.Inputs,                "var_in");
      Serialize (A, V.Outputs,               "var_out");
      Serialize (A, V.Proof_Calls,           "calls_proof");
      Serialize (A, V.Definite_Calls,        "calls");
      Serialize (A, V.Conditional_Calls,     "calls_conditional");
      Serialize (A, V.Local_Variables,       "local_var");
      Serialize (A, V.Local_Subprograms,     "local_sub");
      if V.Kind in Kind_Package | Kind_Package_Body then
         Serialize (A, V.Local_Definite_Writes, "local_init");
      end if;
   end Serialize;

   procedure Serialize (A : in out Archive; V : in out ALI_Entry) is
      procedure Serialize is new Serialisation.Serialize_Discrete
        (T => ALI_Entry_Kind);

      procedure Serialize is new Serialisation.Serialize_Discrete
        (T => Priority_Kind);

      procedure Serialize is new Serialisation.Serialize_Discrete
        (T => Int);

      procedure Serialize is new Serialisation.Serialize_List
        (T              => Name_Lists.List,
         E              => Entity_Name,
         Cursor         => Name_Lists.Cursor,
         Null_Container => Name_Lists.Empty_List,
         Null_Element   => Invalid_Entity_Name,
         First          => Name_Lists.First,
         Next           => Name_Lists.Next,
         Length         => Name_Lists.Length,
         Element        => Name_Lists.Element,
         Append         => Name_Lists.Append,
         Serialize      => Serialize);

      Kind : ALI_Entry_Kind := ALI_Entry_Kind'First;

   --  Start of processing for Serialize

   begin
      if A.Kind = Serialisation.Output then
         Kind := V.Kind;
      end if;
      Serialize (A, Kind);
      if A.Kind = Serialisation.Input then
         V := Null_ALI_Entry (Kind);
      end if;

      case V.Kind is
         when EK_Error =>
            raise Program_Error;

         when EK_End_Marker =>
            null;

         when EK_State_Map =>
            Serialize (A, V.The_State);
            Serialize (A, V.The_Constituents);

         when EK_Remote_States =>
            Serialize (A, V.The_Remote_States, "RS");

         when EK_Volatiles =>
            Serialize (A, V.The_Async_Readers,    "AR");
            Serialize (A, V.The_Async_Writers,    "AW");
            Serialize (A, V.The_Effective_Reads,  "ER");
            Serialize (A, V.The_Effective_Writes, "EW");

         when EK_Globals =>
            Serialize (A, V.The_Global_Info);

         when EK_Protected_Instance =>
            Serialize (A, V.The_Variable);
            Serialize (A, V.The_Priority.Kind);
            if V.The_Priority.Kind = Static then
               Serialize (A, V.The_Priority.Value);
            end if;

         when EK_Task_Instance =>
            Serialize (A, V.The_Type);
            Serialize (A, V.The_Object);

         when EK_Tasking_Info =>
            Serialize (A, V.The_Entity);
            Serialize (A, V.The_Tasking_Info);

         when EK_Nonblocking =>
            Serialize (A, V.The_Nonblocking_Subprograms);

         when EK_Nonreturning =>
            Serialize (A, V.The_Nonreturning_Subprograms);

         when EK_Direct_Calls =>
            Serialize (A, V.The_Caller);
            Serialize (A, V.The_Callees);
      end case;

   exception
      when Serialisation.Parse_Error =>
         pragma Assert (A.Kind = Serialisation.Input);
         V := (Kind => EK_Error);
   end Serialize;

end Flow_Generated_Globals.ALI_Serialization;
