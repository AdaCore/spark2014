------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--      F L O W . C O N T R O L _ F L O W _ G R A P H . U T I L I T Y       --
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

with Sinfo; use Sinfo;

--  with Treepr; use Treepr;

--  with Why;

package body Flow.Control_Flow_Graph.Utility is

   ---------------------------
   -- Make_Basic_Attributes --
   ---------------------------

   function Make_Basic_Attributes
     (Var_Def : Flow_Id_Sets.Set  := Flow_Id_Sets.Empty_Set;
      Var_Use : Flow_Id_Sets.Set  := Flow_Id_Sets.Empty_Set;
      Loops   : Node_Sets.Set     := Node_Sets.Empty_Set;
      E_Loc   : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      A : V_Attributes := Null_Attributes;
   begin
      A.Is_Program_Node   := True;
      A.Variables_Defined := Var_Def;
      A.Variables_Used    := Var_Use;
      A.Loops             := Loops;
      A.Error_Location    := E_Loc;

      return A;
   end Make_Basic_Attributes;

   --------------------------
   -- Make_Call_Attributes --
   --------------------------

   function Make_Call_Attributes
     (Callsite : Node_Id           := Empty;
      Loops    : Node_Sets.Set     := Node_Sets.Empty_Set;
      E_Loc    : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      A : V_Attributes := Null_Attributes;

      Called_Procedure : constant Entity_Id := Entity (Name (Callsite));
      Procedure_Spec   : constant Node_Id   := Parent (Called_Procedure);
   begin
      pragma Assert (Nkind (Procedure_Spec) = N_Procedure_Specification);

      A.Is_Program_Node := True;
      A.Loops           := Loops;
      A.Is_Callsite     := True;
      A.Error_Location  := E_Loc;

      --  case Nkind (Parent (Procedure_Spec)) is
      --     when N_Subprogram_Body =>
      --        A.Perform_IPFA := True;
      --     when N_Subprogram_Declaration =>
      --        A.Perform_IPFA :=
      --          Corresponding_Body (Parent (Procedure_Spec)) /= Empty;
      --     when others =>
      --        Print_Node_Subtree (Parent (Procedure_Spec));
      --        raise Why.Not_Implemented;
      --  end case;

      return A;
   end Make_Call_Attributes;

   -------------------------------
   -- Make_Parameter_Attributes --
   -------------------------------

   function Make_Parameter_Attributes
     (Call_Vertex : Node_Id;
      Actual      : Node_Id;
      Formal      : Node_Id;
      In_Vertex   : Boolean;
      Loops       : Node_Sets.Set;
      E_Loc       : Node_Or_Entity_Id := Empty)
     return V_Attributes
   is
      A : V_Attributes := Null_Attributes;
   begin
      A.Is_Parameter     := True;
      A.Call_Vertex      := Direct_Mapping_Id (Call_Vertex);
      A.Parameter_Actual := Direct_Mapping_Id (Actual);
      A.Parameter_Formal := Direct_Mapping_Id (Formal);
      A.Loops            := Loops;
      A.Error_Location   := E_Loc;

      if In_Vertex then
         pragma Assert (Ekind (Formal) = E_In_Parameter or
                          Ekind (Formal) = E_In_Out_Parameter);
         A.Variables_Used := Get_Variable_Set (Actual);
      else
         pragma Assert (Ekind (Formal) = E_Out_Parameter or
                          Ekind (Formal) = E_In_Out_Parameter);
         A.Variables_Defined := Get_Variable_Set (Actual);
      end if;

      return A;
   end Make_Parameter_Attributes;

   ----------------------------
   -- Make_Global_Attributes --
   ----------------------------

   function Make_Global_Attributes
     (Call_Vertex : Node_Id;
      Global      : Flow_Id;
      Loops       : Node_Sets.Set;
      E_Loc       : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      A : V_Attributes := Null_Attributes;
   begin
      A.Is_Global_Parameter := True;
      A.Call_Vertex         := Direct_Mapping_Id (Call_Vertex);
      A.Parameter_Formal    := Global;
      A.Loops               := Loops;
      A.Error_Location      := E_Loc;

      case Global.Variant is
         when In_View =>
            A.Variables_Used :=
              Flow_Id_Sets.To_Set (Change_Variant (Global, Normal_Use));
         when Out_View =>
            A.Variables_Defined :=
              Flow_Id_Sets.To_Set (Change_Variant (Global, Normal_Use));
         when others =>
            raise Program_Error;
      end case;

      return A;
   end Make_Global_Attributes;

   ------------------------------
   -- Make_Variable_Attributes --
   ------------------------------

   function Make_Variable_Attributes
     (E       : Entity_Id;
      Variant : Initial_Or_Final_Variant;
      E_Loc   : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      A : V_Attributes := Null_Attributes;
   begin
      A.Error_Location := E_Loc;
      A.Is_Constant    :=
        Ekind (E) = E_In_Parameter or
        Ekind (E) = E_Loop_Parameter;

      case Variant is
         when Initial_Value =>
            A.Is_Initialised :=
              Ekind (E) = E_In_Out_Parameter or
              Ekind (E) = E_In_Parameter or
              Ekind (E) = E_Loop_Parameter;

            A.Is_Loop_Parameter := Ekind (E) = E_Loop_Parameter;

            A.Variables_Defined := Flow_Id_Sets.To_Set (Direct_Mapping_Id (E));

         when Final_Value =>
            A.Is_Export :=
              Ekind (E) = E_In_Out_Parameter or
              Ekind (E) = E_Out_Parameter or
              Ekind (E) = E_Function;

            A.Variables_Used := Flow_Id_Sets.To_Set (Direct_Mapping_Id (E));
      end case;

      return A;
   end Make_Variable_Attributes;

   -------------------------------------
   -- Make_Global_Variable_Attributes --
   -------------------------------------

   function Make_Global_Variable_Attributes
     (F       : Flow_Id;
      Mode    : Global_Modes;
      E_Loc   : Node_Or_Entity_Id := Empty)
      return V_Attributes is
      A : V_Attributes := Null_Attributes;
   begin
      A.Error_Location := E_Loc;
      A.Is_Global      := True;
      A.Is_Constant    := Mode in In_Global_Modes;

      case F.Variant is
         when Initial_Value =>
            A.Is_Initialised    := Mode in Initialised_Global_Modes;
            A.Variables_Defined :=
              Flow_Id_Sets.To_Set (Change_Variant (F, Normal_Use));

         when Final_Value =>
            A.Is_Export      := Mode in Exported_Global_Modes;
            A.Variables_Used :=
              Flow_Id_Sets.To_Set (Change_Variant (F, Normal_Use));

         when others =>
            raise Program_Error;
      end case;

      return A;
   end Make_Global_Variable_Attributes;

end Flow.Control_Flow_Graph.Utility;
