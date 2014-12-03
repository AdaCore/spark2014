------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    F L O W _ T R E E _ U T I L I T Y                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--               Copyright (C) 2013-2014, Altran UK Limited                 --
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

with Ada.Strings.Unbounded;  use Ada.Strings.Unbounded;
with Ada.Characters.Latin_1;
with Ada.Strings.Maps;

with Sem_Util;   use Sem_Util;
with Uintp;      use Uintp;

with Output;     use Output;
with Treepr;     use Treepr;

with Why;
--  For the exceptions

--  with SPARK_Util; use SPARK_Util;
with SPARK_Definition; use SPARK_Definition;
with Common_Containers; use Common_Containers;

with Graph;

package body Flow_Tree_Utility is

   Record_Component_Debug : constant Boolean := False;

   package Component_Graphs is new Graph (Vertex_Key   => Entity_Id,
                                          Edge_Colours => Natural,
                                          Null_Key     => Empty,
                                          Test_Key     => "=");

   Comp_Graph  : Component_Graphs.T;

   Temp_String : Unbounded_String := Null_Unbounded_String;

   procedure Add_To_Temp_String (S : String);
   --  Nasty nasty hack to add the given string to a global variable,
   --  Temp_String. We use this to pretty print nodes via Sprint_Node.

   -------------------------
   -- Add_To_Temp_String  --
   -------------------------

   procedure Add_To_Temp_String (S : String) is
      Whitespace : constant Ada.Strings.Maps.Character_Set :=
        Ada.Strings.Maps.To_Set
        (" " & Ada.Characters.Latin_1.CR & Ada.Characters.Latin_1.LF);
   begin
      Append (Temp_String,
              Trim (To_Unbounded_String (S), Whitespace, Whitespace));
      Append (Temp_String, '\');
      Append (Temp_String, 'n');
   end Add_To_Temp_String;

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize
   is
      use Component_Graphs;

      function Node_Info (G : T'Class;
                          V : Vertex_Id)
                          return Node_Display_Info;

      function Edge_Info (G      : T'Class;
                          A      : Vertex_Id;
                          B      : Vertex_Id;
                          Marked : Boolean;
                          Colour : Natural)
                          return Edge_Display_Info;

      function Node_Info (G : T'Class;
                          V : Vertex_Id)
                          return Node_Display_Info
      is
      begin
         Temp_String := Null_Unbounded_String;
         Set_Special_Output (Add_To_Temp_String'Access);
         Print_Tree_Node (G.Get_Key (V));
         Cancel_Special_Output;

         return (Show   => True,
                 Shape  => Shape_Oval,
                 Colour => To_Unbounded_String ("black"),
                 Label  => Temp_String);
      end Node_Info;

      function Edge_Info (G      : T'Class;
                          A      : Vertex_Id;
                          B      : Vertex_Id;
                          Marked : Boolean;
                          Colour : Natural)
                          return Edge_Display_Info
      is
         pragma Unreferenced (G, A, B, Marked, Colour);
      begin
         return (Show   => True,
                 Shape  => Edge_Normal,
                 Colour => To_Unbounded_String ("black"),
                 Label  => Null_Unbounded_String);
      end Edge_Info;

      Ptr  : Entity_Id;
      Ptr2 : Entity_Id;

      S    : Node_Sets.Set;
   begin
      Comp_Graph := Component_Graphs.Create;

      S := Node_Sets.Empty_Set;
      for E of Entity_Set loop
         if Ekind (E) in Record_Kind then
            Ptr := First_Component_Or_Discriminant (E);
            while Present (Ptr) loop
               if not S.Contains (Ptr) then
                  S.Include (Ptr);
                  Comp_Graph.Add_Vertex (Ptr);
               end if;
               if Present (Original_Record_Component (Ptr))
                 and then not S.Contains (Original_Record_Component (Ptr))
               then
                  S.Include (Original_Record_Component (Ptr));
                  Comp_Graph.Add_Vertex (Original_Record_Component (Ptr));
               end if;
               if Ekind (Ptr) = E_Discriminant
                 and then Present (Corresponding_Discriminant (Ptr))
                 and then not S.Contains (Corresponding_Discriminant (Ptr))
               then
                  S.Include (Corresponding_Discriminant (Ptr));
                  Comp_Graph.Add_Vertex (Corresponding_Discriminant (Ptr));
               end if;
               Next_Component_Or_Discriminant (Ptr);
            end loop;
         end if;
      end loop;

      S := Node_Sets.Empty_Set;
      for V of Comp_Graph.Get_Collection (All_Vertices) loop
         Ptr := Comp_Graph.Get_Key (V);
         S.Include (Ptr);
         if Present (Original_Record_Component (Ptr)) then
            Comp_Graph.Add_Edge (V_1    => Ptr,
                                 V_2    => Original_Record_Component (Ptr),
                                 Colour => 0);
         end if;
         case Ekind (Ptr) is
            when E_Discriminant =>
               if Present (Corresponding_Discriminant (Ptr)) then
                  Comp_Graph.Add_Edge
                    (V_1    => Ptr,
                     V_2    => Corresponding_Discriminant (Ptr),
                     Colour => 0);
               end if;
            when E_Component =>
               null;
            when others =>
               raise Program_Error;
         end case;
         for V2 of Comp_Graph.Get_Collection (All_Vertices) loop
            exit when V = V2;
            Ptr2 := Comp_Graph.Get_Key (V2);
            if Sloc (Ptr) = Sloc (Ptr2) then
               Comp_Graph.Add_Edge (V_1    => V,
                                    V_2    => V2,
                                    Colour => 0);
            end if;
         end loop;
      end loop;

      declare
         C         : Cluster_Id;
         Work_List : Node_Sets.Set;
      begin
         while not S.Is_Empty loop
            --  Pick an element at random.
            Ptr := Node_Sets.Element (S.First);
            S.Exclude (Ptr);

            --  Create a new component.
            Comp_Graph.New_Cluster (C);

            --  Seed the work list.
            Work_List := Node_Sets.To_Set (Ptr);

            --  Flood current component.
            while not Work_List.Is_Empty loop
               Ptr := Node_Sets.Element (Work_List.First);
               S.Exclude (Ptr);
               Work_List.Exclude (Ptr);

               Comp_Graph.Set_Cluster (Comp_Graph.Get_Vertex (Ptr), C);

               for Neighbour_Kind in Collection_Type_T range
                 Out_Neighbours .. In_Neighbours
               loop
                  for V of Comp_Graph.Get_Collection
                    (Comp_Graph.Get_Vertex (Ptr), Neighbour_Kind)
                  loop
                     Ptr := Comp_Graph.Get_Key (V);
                     if S.Contains (Ptr) then
                        Work_List.Include (Ptr);
                     end if;
                  end loop;
               end loop;
            end loop;
         end loop;
      end;

      if Record_Component_Debug then
         Comp_Graph.Write_Pdf_File (Filename  => "component_graph",
                                    Node_Info => Node_Info'Access,
                                    Edge_Info => Edge_Info'Access);
      end if;

      Init_Done := True;
   end Initialize;

   ---------------------------------
   -- Get_Procedure_Specification --
   ---------------------------------

   function Get_Procedure_Specification (E : Entity_Id) return Node_Id is
      N : Node_Id;
   begin
      N := Parent (E);
      case Nkind (N) is
         when N_Defining_Program_Unit_Name =>
            return Parent (N);
         when N_Procedure_Specification =>
            return N;
         when others =>
            raise Program_Error;
      end case;
   end Get_Procedure_Specification;

   -------------------
   -- Might_Be_Main --
   -------------------

   function Might_Be_Main (E : Entity_Id) return Boolean is
   begin
      return (Scope_Depth_Value (E) = Uint_1 or else
                (Is_Generic_Instance (E) and then
                   Scope_Depth_Value (E) = Uint_2))
        and then No (First_Formal (E));
   end Might_Be_Main;

   ----------------------
   -- Is_Package_State --
   ----------------------

   function Is_Package_State (E : Entity_Id) return Boolean is
   begin
      case Ekind (E) is
         when E_Abstract_State =>
            return True;

         when E_Variable =>
            case Ekind (Scope (E)) is
               when E_Package =>
                  return True;

               when others =>
                  return False;
            end case;

         when others =>
            return False;
      end case;
   end Is_Package_State;

   --------------
   -- Get_Body --
   --------------

   function Get_Body (E : Entity_Id) return Entity_Id
   is
      Body_N : constant Node_Id := Sem_Util.Get_Subprogram_Body (E);

      Ptr : Node_Id;
   begin
      if No (Body_N) or else Nkind (Body_N) /= N_Subprogram_Body then
         return Empty;
      end if;

      if Acts_As_Spec (Body_N) then
         return Empty;
      end if;

      Ptr := Specification (Body_N);
      pragma Assert (Present (Ptr)
                       and then Nkind (Ptr) in N_Subprogram_Specification);

      Ptr := Defining_Unit_Name (Ptr);
      pragma Assert (Present (Ptr)
                       and then Nkind (Ptr) in N_Entity);

      return Ptr;
   end Get_Body;

   -------------------
   -- Get_Enclosing --
   -------------------

   function Get_Enclosing (N : Node_Id; K : Node_Kind) return Node_Id
   is
      Ptr : Node_Id := N;
   begin
      while Present (Ptr) and then Nkind (Ptr) /= K loop
         Ptr := Parent (Ptr);
      end loop;
      return Ptr;
   end Get_Enclosing;

   ------------------
   -- Has_Volatile --
   ------------------

   function Has_Volatile (E : Entity_Id) return Boolean is
   begin
      case Ekind (E) is
         when E_Abstract_State =>
            return Is_External_State (E);
         when others =>
            return Is_Effectively_Volatile (E);
      end case;
   end Has_Volatile;

   -------------------------
   -- Has_Volatile_Aspect --
   -------------------------

   function Has_Volatile_Aspect (E : Entity_Id;
                                 A : Pragma_Id)
                                 return Boolean
   is
      function Has_Specific_Aspect (E : Entity_Id;
                                    A : Pragma_Id)
                                    return Boolean
      is (case A is
            when Pragma_Async_Readers =>
               Async_Readers_Enabled (E),
            when Pragma_Async_Writers =>
               Async_Writers_Enabled (E),
            when Pragma_Effective_Reads =>
               Effective_Reads_Enabled (E),
            when Pragma_Effective_Writes =>
               Effective_Writes_Enabled (E),
            when others =>
               raise Why.Unexpected_Node);
   begin
      case Ekind (E) is
         when E_Abstract_State =>
            case A is
               when Pragma_Async_Writers =>
                  return Async_Writers_Enabled (E);
               when Pragma_Effective_Reads =>
                  return Effective_Reads_Enabled (E);
               when Pragma_Async_Readers =>
                  return Async_Readers_Enabled (E);
               when Pragma_Effective_Writes =>
                  return Effective_Writes_Enabled (E);
               when others =>
                  raise Program_Error;
            end case;

         when E_In_Parameter =>
            case A is
               when Pragma_Async_Writers =>
                  return True;
               when Pragma_Async_Readers    |
                    Pragma_Effective_Reads  |
                    Pragma_Effective_Writes =>
                  return False;
               when others =>
                  raise Program_Error;
            end case;

         when E_Out_Parameter =>
            case A is
               when Pragma_Async_Writers | Pragma_Effective_Reads =>
                  return False;
               when Pragma_Async_Readers | Pragma_Effective_Writes =>
                  return True;
               when others =>
                  raise Program_Error;
            end case;

         when E_In_Out_Parameter =>
            return True;

         when E_Variable =>
            return Has_Specific_Aspect (E, A);

         when E_Constant =>
            --  SRM 7.1.3(6): A constant, a discriminant or a loop
            --  parameter shall not be Volatile.
            return False;

         when others =>
            Print_Tree_Node (E);
            raise Why.Unexpected_Node;
      end case;
   end Has_Volatile_Aspect;

   --------------------
   -- Component_Hash --
   --------------------

   function Component_Hash (E : Entity_Id) return Ada.Containers.Hash_Type
   is
   begin
      return Ada.Containers.Hash_Type
        (Comp_Graph.Cluster_To_Natural
           (Comp_Graph.Get_Cluster (Comp_Graph.Get_Vertex (E))));
   end Component_Hash;

   --------------------
   -- Same_Component --
   --------------------

   function Same_Component (C1, C2 : Entity_Id) return Boolean
   is
      use Component_Graphs;

      A : constant Cluster_Id :=
        Comp_Graph.Get_Cluster (Comp_Graph.Get_Vertex (C1));
      B : constant Cluster_Id :=
        Comp_Graph.Get_Cluster (Comp_Graph.Get_Vertex (C2));
   begin
      return A = B;
   end Same_Component;

   -----------------------------------
   -- Has_Extensions_Visible_Aspect --
   -----------------------------------

   function Has_Extensions_Visible_Aspect (E : Entity_Id) return Boolean
   is
   begin
      return Present (Get_Pragma (E, Pragma_Extensions_Visible));
   end Has_Extensions_Visible_Aspect;

   ------------------------------------
   -- Get_Full_Type_Without_Checking --
   ------------------------------------

   function Get_Full_Type_Without_Checking (N : Node_Id) return Entity_Id is
      T : constant Entity_Id := Etype (N);
   begin
      if Nkind (N) in N_Entity and then Ekind (N) = E_Abstract_State then
         return T;
      else
         pragma Assert (Nkind (T) in N_Entity);
         pragma Assert (Is_Type (T));
         if Present (Full_View (T)) then
            return Full_View (T);
         else
            return T;
         end if;
      end if;
   end Get_Full_Type_Without_Checking;

end Flow_Tree_Utility;
