------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--  F L O W . G E N E R A T E D _ G L O B A L S . S E R I A L I Z A T I O N --
--                                                                          --
--                                B o d y                                   --
--                                                                          --
--               Copyright (C) 2016-2017, Altran UK Limited                 --
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

   Null_Partial_Contract : constant Partial_Contract :=
     (Name          => Invalid_Entity_Name,
      Local         => Boolean'First,
      Kind          => Entity_Kind'First,
      Origin        => Globals_Origin_T'First,
      Has_Terminate => Boolean'First,
      Nonreturning  => Boolean'First,
      Nonblocking   => Boolean'First,
      others        => <>);
   --  Dummy value required only for the serialization API

   Null_ALI_Entry : constant array (ALI_Entry_Kind) of ALI_Entry :=
     (EK_Error              => (Kind => EK_Error),

      EK_End_Marker         => (Kind => EK_End_Marker),

      EK_State_Map          => (Kind      => EK_State_Map,
                                The_State => Invalid_Entity_Name,
                                others    => <>),

      EK_Remote_States      => (Kind              => EK_Remote_States,
                                The_Remote_States => Name_Sets.Empty_Set),

      EK_Predef_Init_Vars   => (Kind                 => EK_Predef_Init_Vars,
                                The_Predef_Init_Vars => Name_Sets.Empty_Set),

      EK_Volatiles          => (Kind   => EK_Volatiles,
                                others => <>),

      EK_Globals            => (Kind            => EK_Globals,
                                The_Global_Info => Null_Partial_Contract),

      EK_Constant_Calls     => (Kind         => EK_Constant_Calls,
                                The_Constant => Invalid_Entity_Name,
                                The_Calls    => <>),

      EK_Protected_Instance => (Kind         => EK_Protected_Instance,
                                The_Variable => Invalid_Entity_Name,
                                The_Priority => Priority_Value'
                                  (Kind  => Priority_Kind'First,
                                   Value => 0)),

      EK_Task_Instance      => (Kind       => EK_Task_Instance,
                                The_Type   => Invalid_Entity_Name,
                                The_Object => Task_Object'
                                  (Name      => Invalid_Entity_Name,
                                   Instances => 1,
                                   Node      => Empty)),

      EK_Max_Queue_Length   => (Kind                 => EK_Max_Queue_Length,
                                The_Entry            => Invalid_Entity_Name,
                                The_Max_Queue_Length => Nat'First),

      EK_Direct_Calls       => (Kind       => EK_Direct_Calls,
                                The_Caller => Invalid_Entity_Name,
                                others     => <>)
     );
   --  Dummy value required only for the serialization API

   procedure Serialize (A : in out Archive; V : in out Entity_Name);

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

   procedure Serialize (A : in out Archive; V : in out Partial_Contract);

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
      --  Node is a component of the Task_Object record only for convenience;
      --  in phase 1 it is used for debug, in phase 2 it caches the result of
      --  Find_Entity.
      if A.Kind = Serialisation.Input then
         V.Node := Find_Entity (V.Name);
      end if;
   end Serialize;

   procedure Serialize (A : in out Archive; V : in out Partial_Contract) is
      procedure Serialize is new Serialisation.Serialize_Discrete
        (T => Entity_Kind);
      procedure Serialize is new Serialisation.Serialize_Discrete
        (T => Boolean);
      procedure Serialize is new Serialisation.Serialize_Discrete
        (T => Globals_Origin_T);

      procedure Serialize
        (A     : in out Archive;
         G     : in out Global_Names;
         Label : String);

      procedure Serialize (A : in out Archive; V : in out Name_Tasking_Info);

      ---------------
      -- Serialize --
      ---------------

      procedure Serialize
        (A     : in out Archive;
         G     : in out Global_Names;
         Label : String)
      is
      begin
         Serialize (A, G.Proof_Ins, Label & "proof_in");
         Serialize (A, G.Inputs,    Label & "input");
         Serialize (A, G.Outputs,   Label & "output");
      end Serialize;

      procedure Serialize (A : in out Archive; V : in out Name_Tasking_Info) is
      begin
         for Kind in Tasking_Info_Kind loop
            Serialize (A, V (Kind), Kind'Img);
         end loop;
      end Serialize;

   --  Start of processing for Serialize

   begin
      Serialize (A, V.Name);
      Serialize (A, V.Local, "local");
      Serialize (A, V.Kind);
      if V.Kind in E_Function | E_Procedure then
         Serialize (A, V.Is_Protected);
      end if;
      Serialize (A, V.Origin);
      Serialize (A, V.Globals.Proper,  "proper_");  -- ??? replace _ with :
      Serialize (A, V.Globals.Refined, "refined_");
      if V.Kind = E_Package then
         Serialize (A, V.Globals.Initializes, "initializes");
      end if;
      Serialize (A, V.Globals.Calls.Proof_Calls,       "calls_proof");
      Serialize (A, V.Globals.Calls.Definite_Calls,    "calls");
      Serialize (A, V.Globals.Calls.Conditional_Calls, "calls_conditional");
      Serialize (A, V.Local_Variables,         "local_var");
      Serialize (A, V.Local_Ghost_Variables,   "local_ghost");

      if V.Kind in Entry_Kind
                 | E_Function
                 | E_Procedure
                 | E_Task_Type
                 | E_Package
      then
         --  ??? use Is_Proper_Callee here
         if V.Kind /= E_Task_Type then
            Serialize (A, V.Has_Terminate);
            Serialize (A, V.Nonreturning);
            Serialize (A, V.Nonblocking);
         end if;
         Serialize (A, V.Tasking);
      end if;
   end Serialize;

   procedure Serialize (A : in out Archive; V : in out ALI_Entry) is
      procedure Serialize is new Serialisation.Serialize_Discrete
        (T => ALI_Entry_Kind);

      procedure Serialize is new Serialisation.Serialize_Discrete
        (T => Priority_Kind);

      procedure Serialize is new Serialisation.Serialize_Discrete
        (T => Int);

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

         when EK_Predef_Init_Vars =>
            Serialize (A, V.The_Predef_Init_Vars, "PIV");

         when EK_Volatiles =>
            Serialize (A, V.The_Async_Readers,    "AR");
            Serialize (A, V.The_Async_Writers,    "AW");
            Serialize (A, V.The_Effective_Reads,  "ER");
            Serialize (A, V.The_Effective_Writes, "EW");

         when EK_Globals =>
            Serialize (A, V.The_Global_Info);

         when EK_Constant_Calls =>
            Serialize (A, V.The_Constant);
            Serialize (A, V.The_Calls);

         when EK_Protected_Instance =>
            Serialize (A, V.The_Variable);
            Serialize (A, V.The_Priority.Kind);
            if V.The_Priority.Kind = Static then
               Serialize (A, V.The_Priority.Value);
            end if;

         when EK_Task_Instance =>
            Serialize (A, V.The_Type);
            Serialize (A, V.The_Object);

         when EK_Max_Queue_Length =>
            Serialize (A, V.The_Entry);
            Serialize (A, V.The_Max_Queue_Length);

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
