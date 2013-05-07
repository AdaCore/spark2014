------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                       G N A T 2 W H Y . N O D E S                        --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                        Copyright (C) 2012-2013, AdaCore                  --
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

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

with String_Utils;          use String_Utils;

with Csets;                 use Csets;
with Lib;                   use Lib;
with Pprint;                use Pprint;
with Sem_Util;              use Sem_Util;
with Snames;                use Snames;
with Stringt;               use Stringt;
with Urealp;                use Urealp;

with SPARK_Definition;      use SPARK_Definition;
with SPARK_Util;            use SPARK_Util;

with Why.Gen.Names;         use Why.Gen.Names;
with Why.Sinfo;             use Why.Sinfo;
with Why.Inter;             use Why.Inter;

package body Gnat2Why.Nodes is

   function Is_Main_Cunit (N : Node_Id) return Boolean is
     (Get_Cunit_Unit_Number (Parent (N)) = Main_Unit);

   function Is_Spec_Unit_Of_Main_Unit (N : Node_Id) return Boolean is
     (Present (Corresponding_Body (N))
       and then Is_Main_Cunit
        (Unit (Enclosing_Comp_Unit_Node (Corresponding_Body (N)))));

   Why3_Keywords : String_Utils.String_Sets.Set;

   package body Ada_Ent_To_Why is

      -------------
      -- Element --
      -------------

      function Element (M : Map; E : Entity_Id)
                            return Why_Node_Id is
      begin
         return M.Entity_Ids.Element (E);
      end Element;

      function Element (C : Cursor) return Why_Node_Id is
      begin
         case C.Kind is
            when CK_Ent =>
               return Ada_To_Why.Element (C.Ent_Cursor);
            when CK_Str =>
               return Name_To_Why_Map.Element (C.Name_Cursor);
         end case;
      end Element;

      ----------
      -- Find --
      ----------

      function Find (M : Map; E : Entity_Id) return Cursor is
         C : constant Ada_To_Why.Cursor := M.Entity_Ids.Find (E);
      begin
         if Ada_To_Why.Has_Element (C) then
            return Cursor'(CK_Ent,
                           M.Entity_Ids.Find (E),
                           Name_To_Why_Map.No_Element);

            --  We need to check the name map, but before generating a string
            --  to look up, let's check if the map is empty

         elsif Name_To_Why_Map.Is_Empty (M.Entity_Names) then

               --  The dummy cursor

               return Cursor'(CK_Ent, Ada_To_Why.No_Element,
                              Name_To_Why_Map.No_Element);
         else
            declare
               S   : Entity_Name := new String'(Unique_Name (E));
               Res : constant Cursor := Cursor'(CK_Str, Ada_To_Why.No_Element,
                                                M.Entity_Names.Find (S));
            begin
               Free (S);
               return Res;
            end;
         end if;
      end Find;

      function Find (M : Map; E : String) return Cursor is
      begin
         --  We need to check the name map, but before generating a string to
         --  look up, let's check if the map is empty.

         if Name_To_Why_Map.Is_Empty (M.Entity_Names) then

               --  The dummy cursor

               return Cursor'(CK_Ent, Ada_To_Why.No_Element,
                              Name_To_Why_Map.No_Element);
         else
            declare
               S   : Entity_Name := new String'(E);
               Res : constant Cursor := Cursor'(CK_Str, Ada_To_Why.No_Element,
                                                M.Entity_Names.Find (S));
            begin
               Free (S);
               return Res;
            end;
         end if;
      end Find;

      -----------------
      -- Has_Element --
      -----------------

      function Has_Element (M : Map; E : Entity_Id) return Boolean
      is
      begin
         return M.Entity_Ids.Contains (E);
      end Has_Element;

      function Has_Element (C : Cursor) return Boolean
      is
      begin
         case C.Kind is
            when CK_Ent =>
               return Ada_To_Why.Has_Element (C.Ent_Cursor);
            when CK_Str =>
               return Name_To_Why_Map.Has_Element (C.Name_Cursor);
         end case;
      end Has_Element;

      ------------
      -- Insert --
      ------------

      procedure Insert (M : in out Map;
                        E : Entity_Id;
                        W : Why_Node_Id) is
      begin
         M.Entity_Ids.Insert (E, W);
      end Insert;

      procedure Insert (M : in out Map;
                        E : String;
                        W : Why_Node_Id) is
      begin
         M.Entity_Names.Insert (new String'(E), W);
      end Insert;

   end Ada_Ent_To_Why;

   ------------------
   -- Add_To_Graph --
   ------------------

   procedure Add_To_Graph (Map : in out Node_Graphs.Map; From, To : Node_Id) is

      procedure Add_To_Set (Ignored : Node_Id; Set : in out Node_Sets.Set);
      --  Add entity To to set Set

      ----------------
      -- Add_To_Set --
      ----------------

      procedure Add_To_Set (Ignored : Node_Id; Set : in out Node_Sets.Set)
      is
         pragma Unreferenced (Ignored);
      begin
         Set.Include (To);
      end Add_To_Set;

   --  Start of processing for Add_To_Graph

   begin
      if Map.Contains (From) then
         Map.Update_Element (Map.Find (From), Add_To_Set'Access);
      else
         declare
            S : Node_Sets.Set;
         begin
            S.Include (To);
            Map.Insert (From, S);
         end;
      end if;
   end Add_To_Graph;

   ------------------------
   -- Avoid_Why3_Keyword --
   ------------------------

   function Avoid_Why3_Keyword (S : String) return String is
      S_Copy : String := S;
   begin
      Lower_Case_First (S_Copy);
      if Why3_Keywords.Contains (S_Copy) then
         return S_Copy & "__";
      else
         return S_Copy;
      end if;
   end Avoid_Why3_Keyword;

   -----------------------------------
   -- Body_File_Name_Without_Suffix --
   -----------------------------------

   function Body_File_Name_Without_Suffix (N : Node_Id) return String
   is
      CU       : Node_Id := Enclosing_Comp_Unit_Node (N);
      Switch   : Boolean := False;
   begin
      case Nkind (Unit (CU)) is
         when N_Package_Body    |
              N_Subprogram_Body |
              N_Subunit         =>
            null;
         when others =>
            Switch := True;
      end case;
      if Switch and then Present (Library_Unit (CU)) then
         CU := Library_Unit (CU);
      end if;
      return File_Name_Without_Suffix (Sloc (CU));
   end Body_File_Name_Without_Suffix;

   -----------------------
   -- Get_Graph_Closure --
   -----------------------

   function Get_Graph_Closure
     (Map  : Node_Graphs.Map;
      From : Node_Id) return Node_Sets.Set
   is
      use Node_Sets;
      Result   : Set;
      Work_Set : Set;
      First    : Cursor;
      Cur_Node : Node_Id;

      procedure Update_Work_Set (Ignored : Node_Id; New_Set : Set);
      --  Update sets Result and Work_Set by adding those nodes from New_Set
      --  that have not been encountered yet.

      ---------------------
      -- Update_Work_Set --
      ---------------------

      procedure Update_Work_Set (Ignored : Node_Id; New_Set : Set) is
         pragma Unreferenced (Ignored);
      begin
         for N of New_Set loop
            if not Result.Contains (N) then
               Result.Include (N);
               Work_Set.Include (N);
            end if;
         end loop;
      end Update_Work_Set;

   begin
      Work_Set.Include (From);
      Result.Include (From);

      while not Work_Set.Is_Empty loop
         First := Work_Set.First;
         Cur_Node := Element (First);
         Work_Set.Delete (First);

         if Map.Contains (Cur_Node) then
            Node_Graphs.Query_Element (Position => Map.Find (Cur_Node),
                                       Process  => Update_Work_Set'Access);
         end if;
      end loop;

      return Result;
   end Get_Graph_Closure;

   ---------------
   -- Get_Range --
   ---------------

   function Get_Range (N : Node_Id) return Node_Id is
   begin
      case Nkind (N) is
         when N_Range                           |
              N_Real_Range_Specification        |
              N_Signed_Integer_Type_Definition  |
              N_Modular_Type_Definition         |
              N_Floating_Point_Definition       |
              N_Ordinary_Fixed_Point_Definition |
              N_Decimal_Fixed_Point_Definition  =>
            return N;

         when N_Subtype_Indication =>
            return Range_Expression (Constraint (N));

         when N_Identifier | N_Expanded_Name =>
            return Get_Range (Entity (N));

         when N_Defining_Identifier =>
            case Ekind (N) is
               when Scalar_Kind =>
                  return Get_Range (Scalar_Range (N));

               when Object_Kind =>
                  return Get_Range (Scalar_Range (Etype (N)));

               when others =>
                  raise Program_Error;
            end case;

         when others =>
            raise Program_Error;
      end case;
   end Get_Range;

   ----------------------
   -- Has_Precondition --
   ----------------------

   function Has_Precondition (E : Entity_Id) return Boolean is
      PPC      : Node_Id;
   begin
      PPC := Pre_Post_Conditions (Contract (E));
      while Present (PPC) loop
         if Pragma_Name (PPC) = Name_Precondition then
            return True;
         end if;
         PPC := Next_Pragma (PPC);
      end loop;
      return False;
   end Has_Precondition;

   -----------------------
   -- In_Main_Unit_Body --
   -----------------------

   function In_Main_Unit_Body (N : Node_Id) return Boolean is
      CU   : constant Node_Id := Enclosing_Comp_Unit_Node (N);
      Root : Node_Id;

   begin
      if No (CU) then
         return False;
      end if;

      Root := Unit (CU);

      case Nkind (Root) is
         when N_Package_Body    |
              N_Subprogram_Body =>

            return Is_Main_Cunit (Root);

         --  The only way a node in a subunit can be seen is when this subunit
         --  is part of the main unit.

         when N_Subunit =>
            return True;

         when N_Package_Declaration            |
              N_Generic_Package_Declaration    |
              N_Subprogram_Declaration         |
              N_Generic_Subprogram_Declaration =>

            return False;

         when N_Package_Renaming_Declaration           |
              N_Generic_Package_Renaming_Declaration   |
              N_Subprogram_Renaming_Declaration        |
              N_Generic_Function_Renaming_Declaration  |
              N_Generic_Procedure_Renaming_Declaration =>

            return False;

         when others =>
            raise Program_Error;
      end case;
   end In_Main_Unit_Body;

   -----------------------
   -- In_Main_Unit_Spec --
   -----------------------

   function In_Main_Unit_Spec (N : Node_Id) return Boolean is
      CU   : constant Node_Id := Enclosing_Comp_Unit_Node (N);
      Root : Node_Id;

   begin
      if No (CU) then
         return False;
      end if;

      Root := Unit (CU);

      case Nkind (Root) is
         when N_Package_Body    |
              N_Subprogram_Body |
              N_Subunit         =>

            return False;

         when N_Package_Declaration            |
              N_Generic_Package_Declaration    |
              N_Subprogram_Declaration         |
              N_Generic_Subprogram_Declaration =>

            return Is_Main_Cunit (Root)
              or else Is_Spec_Unit_Of_Main_Unit (Root);

         when N_Package_Renaming_Declaration           |
              N_Generic_Package_Renaming_Declaration   |
              N_Subprogram_Renaming_Declaration        |
              N_Generic_Function_Renaming_Declaration  |
              N_Generic_Procedure_Renaming_Declaration =>

            return False;

         when others =>
            raise Program_Error;
      end case;
   end In_Main_Unit_Spec;

   -----------------------
   -- In_Some_Unit_Body --
   -----------------------

   function In_Some_Unit_Body (N : Node_Id) return Boolean is
      CU   : constant Node_Id := Enclosing_Comp_Unit_Node (N);
      Root : Node_Id;

   begin
      if No (CU) then
         return False;
      end if;

      Root := Unit (CU);

      return Nkind (Root) in N_Unit_Body
        or else Nkind (Root) = N_Subunit;
   end In_Some_Unit_Body;

   ------------------------
   -- Is_In_Current_Unit --
   ------------------------

   function Is_In_Current_Unit (N : Node_Id) return Boolean is
      Real_Node : constant Node_Id :=
        (if Is_Itype (N) then Associated_Node_For_Itype (N) else N);
   begin

      --  ??? Should be made more efficient

      return In_Main_Unit_Spec (Real_Node) or else
        In_Main_Unit_Body (Real_Node);
   end Is_In_Current_Unit;

   function Is_Pragma_Assert_And_Cut (N : Node_Id) return Boolean
   is
      Orig : constant Node_Id := Original_Node (N);
   begin
      return
        (Present (Orig) and then
         Nkind (Orig) = N_Pragma and then
         Get_Name_String (Chars (Pragma_Identifier (Orig))) =
           "assert_and_cut");
   end Is_Pragma_Assert_And_Cut;

   ------------------------------
   -- Is_Quantified_Loop_Param --
   ------------------------------

   function Is_Quantified_Loop_Param (E : Entity_Id) return Boolean is
   begin
      return
        (Present (Scope (E)) and then
         Present (Parent (Scope (E))) and then
         Nkind (Parent (Scope (E))) = N_Quantified_Expression);
   end Is_Quantified_Loop_Param;

   -----------------
   -- Source_Name --
   -----------------

   function Source_Name (E : Entity_Id) return String is
      function Short_Name (E : Entity_Id) return String;

      ----------------
      -- Short_Name --
      ----------------

      function Short_Name (E : Entity_Id) return String is
      begin
         Get_Unqualified_Name_String (Chars (E));
         return Name_Buffer (1 .. Name_Len);
      end Short_Name;

   begin
      if not (Comes_From_Source (E)) then
         return Short_Name (E);
      else
         declare
            Sl   : Source_Ptr := Sloc (E);
            TBuf : constant Source_Buffer_Ptr :=
              Source_Text (Get_Source_File_Index (Sl));
            Buf  : Unbounded_String := Null_Unbounded_String;
         begin
            if TBuf (Sl) = '"' then
               return Short_Name (E);
            end if;
            while Identifier_Char (TBuf (Sl)) loop
               Append (Buf, TBuf (Sl));
               Sl := Sl + 1;
            end loop;
            return To_String (Buf);
         end;
      end if;
   end Source_Name;

   ----------------
   -- Short_Name --
   ----------------

   function Short_Name (E : Entity_Id) return String
   is
   begin
      return Avoid_Why3_Keyword (Get_Name_String (Chars (E)));
   end Short_Name;

   -----------------------------------
   -- Spec_File_Name_Without_Suffix --
   -----------------------------------

   function Spec_File_Name_Without_Suffix (N : Node_Id) return String
   is
      CU       : Node_Id := Enclosing_Comp_Unit_Node (N);
   begin
      case Nkind (Unit (CU)) is
         when N_Package_Body | N_Subunit =>
            CU := Library_Unit (CU);
         when others =>
            null;
      end case;
      return File_Name_Without_Suffix (Sloc (CU));
   end Spec_File_Name_Without_Suffix;

   --------------------
   -- String_Of_Node --
   --------------------

   function String_Of_Node (N : Node_Id) return String
   is

      function Real_Image (U : Ureal) return String;
      function String_Image (S : String_Id) return String;
      function Ident_Image (Expr        : Node_Id;
                            Orig_Expr   : Node_Id;
                            Expand_Type : Boolean)
                            return String;

      function Node_To_String is new
        Expression_Image (Real_Image, String_Image, Ident_Image);
      --  The actual printing function

      -----------------
      -- Ident_Image --
      -----------------

      function Ident_Image (Expr        : Node_Id;
                            Orig_Expr   : Node_Id;
                            Expand_Type : Boolean)
                            return String
      is
         pragma Unreferenced (Orig_Expr, Expand_Type);
      begin
         if Nkind (Expr) = N_Defining_Identifier then
            return Source_Name (Expr);
         elsif Present (Entity (Expr)) then
            return Source_Name (Entity (Expr));
         else
            return Get_Name_String (Chars (Expr));
         end if;
      end Ident_Image;

      ----------------
      -- Real_Image --
      ----------------

      function Real_Image (U : Ureal) return String is
      begin
         pragma Unreferenced (U);
         --  ??? still to be done
         return "";
      end Real_Image;

      ------------------
      -- String_Image --
      ------------------

      function String_Image (S : String_Id) return String is
      begin
         Name_Len := 0;
         Add_Char_To_Name_Buffer ('"');
         Add_String_To_Name_Buffer (S);
         Add_Char_To_Name_Buffer ('"');
         return Name_Buffer (1 .. Name_Len);
      end String_Image;

   begin
      return Node_To_String (N, "");
   end String_Of_Node;

   ---------------------------------
   -- Subprogram_Full_Source_Name --
   ---------------------------------

   function Subprogram_Full_Source_Name (E : Entity_Id) return String
   is
      Name : constant String := Source_Name (E);
   begin
      if Has_Fully_Qualified_Name (E)
        or else Scope (E) = Standard_Standard
      then
         return Name;
      else
         return Subprogram_Full_Source_Name (Unique_Entity (Scope (E))) &
           "." & Name;
      end if;
   end Subprogram_Full_Source_Name;

   ------------------
   -- Type_Of_Node --
   ------------------

   function Type_Of_Node (N : Node_Id) return Entity_Id is
      T : Entity_Id;
   begin
      if Nkind (N) in N_Entity then
         if Ekind (N) in Type_Kind then
            T := N;
         else
            T := Etype (N);
         end if;
      elsif Nkind (N) in N_Identifier | N_Expanded_Name then
         T := Etype (Entity (N));
      else
         T := Etype (N);
      end if;

      --  The type of a node is either its most underlying type, or else the
      --  special private type in all other cases, represented in the AST by
      --  its type.

      if In_SPARK (Most_Underlying_Type (T)) then
         return Most_Underlying_Type (T);
      else
         return T;
      end if;
   end Type_Of_Node;

   function Type_Of_Node (N : Node_Id) return String
   is
      E : constant Entity_Id := Type_Of_Node (N);
   begin
      if E = Standard_Boolean then
         return Why_Scalar_Type_Name (EW_Bool);
      elsif E = Universal_Fixed then
         return Why_Scalar_Type_Name (EW_Real);
      else
         return Full_Name (E);
      end if;
   end Type_Of_Node;

   function Type_Of_Node (N : Node_Id) return W_Base_Type_Id
   is
      E : constant Entity_Id := Type_Of_Node (N);
   begin
      if E = Standard_Boolean then
         return EW_Bool_Type;
      elsif E = Universal_Fixed then
         return EW_Real_Type;
      else
         return EW_Abstract (E);
      end if;
   end Type_Of_Node;

begin
   Why3_Keywords.Include ("begin");
   Why3_Keywords.Include ("end");
   Why3_Keywords.Include ("invariant");
   Why3_Keywords.Include ("as");
   Why3_Keywords.Include ("axiom");
   Why3_Keywords.Include ("clone");
   Why3_Keywords.Include ("coinductive");
   Why3_Keywords.Include ("constant");
   Why3_Keywords.Include ("else");
   Why3_Keywords.Include ("end");
   Why3_Keywords.Include ("epsilon");
   Why3_Keywords.Include ("exists");
   Why3_Keywords.Include ("export");
   Why3_Keywords.Include ("false");
   Why3_Keywords.Include ("forall");
   Why3_Keywords.Include ("function");
   Why3_Keywords.Include ("goal");
   Why3_Keywords.Include ("if");
   Why3_Keywords.Include ("import");
   Why3_Keywords.Include ("in");
   Why3_Keywords.Include ("inductive");
   Why3_Keywords.Include ("lemma");
   Why3_Keywords.Include ("let");
   Why3_Keywords.Include ("match");
   Why3_Keywords.Include ("meta");
   Why3_Keywords.Include ("namespace");
   Why3_Keywords.Include ("not");
   Why3_Keywords.Include ("predicate");
   Why3_Keywords.Include ("prop");
   Why3_Keywords.Include ("then");
   Why3_Keywords.Include ("theory");
   Why3_Keywords.Include ("true");
   Why3_Keywords.Include ("type");
   Why3_Keywords.Include ("use");
   Why3_Keywords.Include ("with");
   Why3_Keywords.Include ("abstract");
   Why3_Keywords.Include ("absurd");
   Why3_Keywords.Include ("any");
   Why3_Keywords.Include ("assert");
   Why3_Keywords.Include ("assume");
   Why3_Keywords.Include ("begin");
   Why3_Keywords.Include ("check");
   Why3_Keywords.Include ("do");
   Why3_Keywords.Include ("done");
   Why3_Keywords.Include ("downto");
   Why3_Keywords.Include ("exception");
   Why3_Keywords.Include ("for");
   Why3_Keywords.Include ("fun");
   Why3_Keywords.Include ("ghost");
   Why3_Keywords.Include ("invariant");
   Why3_Keywords.Include ("loop");
   Why3_Keywords.Include ("model");
   Why3_Keywords.Include ("module");
   Why3_Keywords.Include ("mutable");
   Why3_Keywords.Include ("private");
   Why3_Keywords.Include ("raise");
   Why3_Keywords.Include ("raises");
   Why3_Keywords.Include ("reads");
   Why3_Keywords.Include ("rec");
   Why3_Keywords.Include ("to");
   Why3_Keywords.Include ("try");
   Why3_Keywords.Include ("val");
   Why3_Keywords.Include ("variant");
   Why3_Keywords.Include ("while");
   Why3_Keywords.Include ("writes");
   Why3_Keywords.Include ("int");
   Why3_Keywords.Include ("real");
   Why3_Keywords.Include ("bool");
   Why3_Keywords.Include ("unit");
end Gnat2Why.Nodes;
