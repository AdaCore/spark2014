------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                       A L F A . D E F I N I T I O N                      --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                        Copyright (C) 2011-2012, AdaCore                  --
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
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Strings.Fixed;
with Ada.Strings.Maps.Constants;

with Namet;          use Namet;
with Nlists;         use Nlists;
with Sem_Util;       use Sem_Util;
with Sinput;         use Sinput;

with Gnat2Why.Nodes; use Gnat2Why.Nodes;

package body Alfa.Util is

   function File_Is_Formal_Container (Name : String) return Boolean;
   --  Return true when the string in argument is a file of formal container
   --  unit
   ------------------
   -- Global State --
   ------------------

   Full_To_Partial_Entities : Node_Maps.Map;
   --  Map from full views of entities to their partial views, for deferred
   --  constants and private types.

   -------------------------------
   -- Add_Full_And_Partial_View --
   -------------------------------

   procedure Add_Full_And_Partial_View (Full, Partial : Entity_Id) is
   begin
      Full_To_Partial_Entities.Insert (Full, Partial);
   end Add_Full_And_Partial_View;

   ------------------------------------
   -- Aggregate_Is_Fully_Initialized --
   ------------------------------------

   function Aggregate_Is_Fully_Initialized (N : Node_Id) return Boolean is

      function Matching_Component_Association
        (Component   : Entity_Id;
         Association : Node_Id) return Boolean;
      --  Return whether Association matches Component

      ------------------------------------
      -- Matching_Component_Association --
      ------------------------------------

      function Matching_Component_Association
        (Component   : Entity_Id;
         Association : Node_Id) return Boolean
      is
         CL : constant List_Id := Choices (Association);
      begin
         pragma Assert (List_Length (CL) = 1);
         return Component = Entity (First (CL));
      end Matching_Component_Association;

      Typ         : constant Entity_Id := Underlying_Type (Etype (N));
      Assocs      : List_Id;
      Component   : Entity_Id;
      Association : Node_Id;

   --  Start of Aggregate_Is_Fully_Initialized

   begin
      if Is_Record_Type (Typ) then
         pragma Assert (No (Expressions (N)));

         Assocs      := Component_Associations (N);
         Component   := First_Component (Typ);
         Association := First (Assocs);

         while Component /= Empty loop
            if Present (Association)
              and then Matching_Component_Association (Component, Association)
            then
               if Box_Present (Association) then
                  return False;
               end if;
               Next (Association);
            else
               return False;
            end if;
            Component := Next_Component (Component);
         end loop;

      else
         pragma Assert (Is_Array_Type (Typ) or else Is_String_Type (Typ));

         Assocs := Component_Associations (N);

         if Present (Assocs) then
            Association := First (Assocs);

            while Present (Association) loop
               if Box_Present (Association) then
                  return False;
               end if;
               Next (Association);
            end loop;
         end if;
      end if;

      return True;
   end Aggregate_Is_Fully_Initialized;

   ------------------------------------------
   -- All_Aggregates_Are_Fully_Initialized --
   ------------------------------------------

   function All_Aggregates_Are_Fully_Initialized
     (N : Node_Id) return Boolean
   is
      Aggregate_Not_Fully_Initialized : Boolean := False;

      function Check_Aggregate (N : Node_Id) return Traverse_Result;
      --  Set Aggregate_Not_Fully_Initialized to True if N is an aggregate not
      --  fully initialized.

      ---------------------
      -- Check_Aggregate --
      ---------------------

      function Check_Aggregate (N : Node_Id) return Traverse_Result is
      begin
         if Nkind (N) = N_Aggregate
           and then not Aggregate_Is_Fully_Initialized (N)
         then
            Aggregate_Not_Fully_Initialized := True;
            return Abandon;
         else
            return OK;
         end if;
      end Check_Aggregate;

      function Traverse_Aggregate is new Traverse_Func (Check_Aggregate);

      Ignored : Traverse_Final_Result;
      pragma Unreferenced (Ignored);

   begin
      Ignored := Traverse_Aggregate (N);
      return not Aggregate_Not_Fully_Initialized;
   end All_Aggregates_Are_Fully_Initialized;

   --------------------------------------
   -- Expression_Functions_All_The_Way --
   --------------------------------------

   function Expression_Functions_All_The_Way (E : Entity_Id) return Boolean is

      Only_Expression_Functions : Boolean := True;
      --  Set to False if a call to something else than an expression
      --  function is seen.

      Already_Seen : Node_Sets.Set;
      --  Set of functions already seen

      use Node_Sets;

      function Mark_Regular_Call (N : Node_Id) return Traverse_Result;
      --  Basic marking function

      procedure Traverse_Expression_Function (E : Entity_Id);
      --  Main recursive traversal

      -----------------------
      -- Mark_Regular_Call --
      -----------------------

      function Mark_Regular_Call (N : Node_Id) return Traverse_Result is
      begin
         if Nkind_In (N, N_Function_Call, N_Procedure_Call_Statement) then
            declare
               Nam : constant Node_Id := Name (N);
            begin
               if not Is_Entity_Name (Nam)
                 or else No (Entity (Nam))
               then
                  Only_Expression_Functions := False;
               else
                  Traverse_Expression_Function (Entity (Nam));
               end if;
            end;
         end if;
         return OK;
      end Mark_Regular_Call;

      procedure Traverse_And_Mark is new Traverse_Proc (Mark_Regular_Call);

      ----------------------------------
      -- Traverse_Expression_Function --
      ----------------------------------

      procedure Traverse_Expression_Function (E : Entity_Id) is
         Decl      : Node_Id;
         Body_Decl : Node_Id;

      begin
         if Nkind (Parent (E)) = N_Defining_Program_Unit_Name then
            Decl := Parent (Parent (Parent (E)));
         else
            Decl := Parent (Parent (E));
         end if;

         if Nkind (Decl) = N_Subprogram_Body then
            Body_Decl := Decl;
         elsif Present (Corresponding_Body (Decl)) then
            Body_Decl := Parent (Parent (Corresponding_Body (Decl)));
         else
            Body_Decl := Empty;
         end if;

         --  If not possible to follow calls to expression functions further
         --  because function is declared in another unit, consider it may not
         --  be an expression function.

         if No (Body_Decl) then
            Only_Expression_Functions := False;

         elsif Nkind (Original_Node (Decl)) /= N_Expression_Function
           and then Nkind (Original_Node (Body_Decl)) /= N_Expression_Function
         then
            Only_Expression_Functions := False;

         --  Protect against recursion, which cannot introduce more calls

         elsif Contains (Already_Seen, E) then
            null;

         else
            Include (Already_Seen, E);
            Traverse_And_Mark (Parent (Parent (Corresponding_Body (Decl))));
         end if;
      end Traverse_Expression_Function;

   begin
      Traverse_Expression_Function (E);
      return Only_Expression_Functions;
   end Expression_Functions_All_The_Way;

   function Entity_Is_Instance_Of_Formal_Container (Id : Entity_Id)
                                                    return Boolean
   is
   begin
      return File_Is_Formal_Container (File_Name (Sloc (Id)));
   end Entity_Is_Instance_Of_Formal_Container;

   ------------------------------
   -- File_Is_Formal_Container --
   ------------------------------

   function File_Is_Formal_Container (Name : String) return Boolean is
   begin
      return
        Name = "a-cfdlli.ads" or else Name = "a-cfdlli.adb" or else
        Name = "a-cfhama.ads" or else Name = "a-cfhama.adb" or else
        Name = "a-cfhase.ads" or else Name = "a-cfhase.adb" or else
        Name = "a-cforma.ads" or else Name = "a-cforma.adb" or else
        Name = "a-cforse.ads" or else Name = "a-cforse.adb" or else
        Name = "a-cofove.ads" or else Name = "a-cofove.adb";
   end File_Is_Formal_Container;

   -------------------------------
   -- Get_Enclosing_Declaration --
   -------------------------------

   function Get_Enclosing_Declaration (N : Node_Id) return Node_Id is
      Decl_N : Node_Id := N;
   begin
      while Present (Decl_N)
        and then not (Nkind (Decl_N) in N_Declaration
                        or else
                      Nkind (Decl_N) in N_Later_Decl_Item)
      loop
         Decl_N := Parent (Decl_N);
      end loop;
      return Decl_N;
   end Get_Enclosing_Declaration;

   -----------------------------
   -- Get_Expression_Function --
   -----------------------------

   function Get_Expression_Function (E : Entity_Id) return Node_Id is
      Decl_N : constant Node_Id := Parent (Get_Subprogram_Spec (E));
      Body_N : constant Node_Id := Get_Subprogram_Body (E);
      Orig_N : Node_Id;
   begin
      --  Get the original node either from the declaration for E, or from the
      --  subprogram body for E, which may be different if E is attached to a
      --  subprogram declaration.

      if Present (Original_Node (Decl_N))
        and then Original_Node (Decl_N) /= Decl_N
      then
         Orig_N := Original_Node (Decl_N);
      else
         Orig_N := Original_Node (Body_N);
      end if;

      if Nkind (Orig_N) = N_Expression_Function then
         return Orig_N;
      else
         return Empty;
      end if;
   end Get_Expression_Function;

   -------------------------
   -- Get_Subprogram_Body --
   -------------------------

   --  Replace version in Sem_Util with this simpler one ???

   function Get_Subprogram_Body (E : Entity_Id) return Node_Id is
      Body_E : Entity_Id;
      N      : Node_Id;

   begin
      --  Retrieve the declaration for E

      N := Parent (Get_Subprogram_Spec (E));

      --  If this declaration is not a subprogram body, then it must be a
      --  subprogram declaration, from which we can retrieve the entity
      --  for the corresponding subprogram body.

      if Nkind (N) = N_Subprogram_Body then
         Body_E := E;
      else
         Body_E := Corresponding_Body (N);
      end if;

      --  Retrieve the subprogram body

      return Parent (Get_Subprogram_Spec (Body_E));
   end Get_Subprogram_Body;

   -------------------------
   -- Get_Subprogram_Spec --
   -------------------------

   function Get_Subprogram_Spec (E : Entity_Id) return Node_Id is
      N : Node_Id;

   begin
      N := Parent (E);

      if Nkind (N) = N_Defining_Program_Unit_Name then
         N := Parent (N);
      end if;

      return N;
   end Get_Subprogram_Spec;

   ------------------
   -- Is_Full_View --
   ------------------

   function Is_Full_View (E : Entity_Id) return Boolean is
      (Full_To_Partial_Entities.Contains (E));

   ------------------------------------------
   -- Is_Instantiation_Of_Formal_Container --
   ------------------------------------------

   function Is_Instantiation_Of_Formal_Container (N : Node_Id) return Boolean
   is ((Is_Rewrite_Insertion (N)
          or else Nkind (Original_Node (N)) = N_Package_Instantiation)

       --  The Generic_Parent component is not set in some cases, so test its
       --  presence before looking at its source location.

       and then Present (Generic_Parent (Specification (N)))
       and then Location_In_Formal_Containers
                  (Sloc (Generic_Parent (Specification (N)))));

   --------------------------------------------
   -- Is_Access_To_Formal_Container_Capacity --
   --------------------------------------------

   function Is_Access_To_Formal_Container_Capacity (N : Node_Id) return Boolean
   is
      E : constant Entity_Id := Entity (Selector_Name (N));
   begin
      return Ekind (E) = E_Discriminant
        and then Is_Formal_Container_Capacity (E);
   end Is_Access_To_Formal_Container_Capacity;

   ----------------------------------
   -- Is_Formal_Container_Capacity --
   ----------------------------------

   function Is_Formal_Container_Capacity (E : Entity_Id) return Boolean is
      Typ : constant Entity_Id :=
        Most_Underlying_Type
          (Unique_Defining_Entity (Get_Enclosing_Declaration (E)));
      Name : constant String :=
        Ada.Strings.Fixed.Translate
          (Get_Name_String (Chars (E)),
           Ada.Strings.Maps.Constants.Lower_Case_Map);
   begin
      return Location_In_Formal_Containers (Sloc (Typ))
        and then Name = Lowercase_Capacity_Name;
   end Is_Formal_Container_Capacity;

   -----------------------------------
   -- Location_In_Formal_Containers --
   -----------------------------------

   function Location_In_Formal_Containers (Loc : Source_Ptr) return Boolean is
   begin
      if Loc = Standard_Location then
         return False;
      else
         return
           File_Is_Formal_Container
             (Get_Name_String (Reference_Name (Get_Source_File_Index (Loc))));
      end if;
   end Location_In_Formal_Containers;

   -----------------------------
   -- Lowercase_Capacity_Name --
   -----------------------------

   function Lowercase_Capacity_Name return String is ("capacity");

   --------------------------------
   -- Lowercase_Has_Element_Name --
   --------------------------------

   function Lowercase_Has_Element_Name return String is ("has_element");

   ----------------------------
   -- Lowercase_Iterate_Name --
   ----------------------------

   function Lowercase_Iterate_Name return String is ("iterate");

   --------------------------
   -- Most_Underlying_Type --
   --------------------------

   function Most_Underlying_Type (E : Entity_Id) return Entity_Id is
      Typ : Entity_Id := E;
   begin
      loop
         --  For types in formal container instantiations, do not consider the
         --  underlying type.

         if Type_In_Formal_Container (Typ) then
            return Typ;
         elsif Ekind (Typ) in Private_Kind then
            Typ := Underlying_Type (Typ);
         else
            return Typ;
         end if;
      end loop;
   end Most_Underlying_Type;

   ------------------
   -- Partial_View --
   ------------------

   function Partial_View (E : Entity_Id) return Entity_Id is
      (Full_To_Partial_Entities.Element (E));

   ------------------------------------
   -- Type_Based_On_Formal_Container --
   ------------------------------------

   function Type_Based_On_Formal_Container (E : Entity_Id) return Boolean is
     (Present (Underlying_Formal_Container_Type (E)));

   ------------------------------
   -- Type_In_Formal_Container --
   ------------------------------

   function Type_In_Formal_Container (Id : Entity_Id) return Boolean is

      function Name_Ends_With (N, Suffix : String) return Boolean;
      --  Return whether N ends with Suffix, as a means to recognize whether
      --  the full name of entity Id is the completion of a type name which we
      --  handle specially.

      --------------------
      -- Name_Ends_With --
      --------------------

      function Name_Ends_With (N, Suffix : String) return Boolean is
         (Ada.Strings.Fixed.Tail (N, Suffix'Length) = Suffix);

      N : Node_Id := Parent (Id);
      Name : constant String :=
        Ada.Strings.Fixed.Translate
          (Get_Name_String (Chars (Id)),
           Ada.Strings.Maps.Constants.Lower_Case_Map);
   begin
      if Present (N) then
         N := Parent (N);
      end if;

      if Present (N) then
         N := Parent (N);
      end if;

      return Present (N)
        and then Nkind (N) = N_Package_Declaration
        and then Is_Instantiation_Of_Formal_Container (N)
        and then (Name_Ends_With (Name, "list") or else
                  Name_Ends_With (Name, "vector") or else
                  Name_Ends_With (Name, "set") or else
                  Name_Ends_With (Name, "map") or else
                  Name_Ends_With (Name, "key_type") or else
                  Name_Ends_With (Name, "element_type") or else
                  Name_Ends_With (Name, "cursor"));
   end Type_In_Formal_Container;

   --------------------------------------
   -- Underlying_Formal_Container_Type --
   --------------------------------------

   function Underlying_Formal_Container_Type (E : Entity_Id) return Entity_Id
   is
      Typ : Entity_Id := E;
   begin
      loop
         if Type_In_Formal_Container (Typ) then
            return Typ;
         elsif Ekind (Typ) in Private_Kind then
            Typ := Underlying_Type (Typ);
         elsif Ekind (Typ) in Record_Kind then
            if Typ = Base_Type (Typ) then
               return Empty;
            end if;
            Typ := Base_Type (Typ);
         else
            return Empty;
         end if;
      end loop;
   end Underlying_Formal_Container_Type;

end Alfa.Util;
