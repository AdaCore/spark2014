------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--           F L O W . A N A L Y S I S . A N T I A L I A S I N G            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--              Copyright (C) 2013-2023, Capgemini Engineering              --
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

with Atree;               use Atree;
with Ada.Containers;      use Ada.Containers;
with Flow_Classwide;      use Flow_Classwide;
with Flow_Error_Messages; use Flow_Error_Messages;
with Flow_Utility;        use Flow_Utility;
with Namet;               use Namet;
with Nlists;              use Nlists;
with Output;              use Output;
with Sem_Aux;             use Sem_Aux;
with Sem_Eval;            use Sem_Eval;
with Sem_Util;            use Sem_Util;
with Sinfo.Utils;         use Sinfo.Utils;
with Snames;              use Snames;
with Sprint;              use Sprint;
with SPARK_Util;          use SPARK_Util;
with VC_Kinds;            use VC_Kinds;
with Why;

package body Flow.Analysis.Antialiasing is

   Trace_Antialiasing : constant Boolean := False;
   --  Enable this for gratuitous tracing output for aliasing detection

   subtype Computed_Aliasing_Result is Aliasing_Check_Result
     range Impossible .. Definite_Aliasing;

   subtype Non_Obvious_Aliasing_Check_Result is Aliasing_Check_Result
     range No_Aliasing .. Definite_Aliasing;

   package Aliasing_Statuses is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Computed_Aliasing_Result,
      Hash            => Node_Hash,
      Equivalent_Keys => "=");

   Aliasing_Status : Aliasing_Statuses.Map := Aliasing_Statuses.Empty_Map;

   function Check_Ranges (Range_A : Node_Id;
                          Range_B : Node_Id)
                          return Non_Obvious_Aliasing_Check_Result;
   --  Checks two ranges for potential overlap

   function Aliasing (A,        B        : Node_Id;
                      Formal_A, Formal_B : Entity_Id)
                      return Computed_Aliasing_Result
   with Pre => Is_Formal (Formal_A)
               and then (No (Formal_B) or else Is_Formal (Formal_B));
   --  Returns if A and B alias

   function Is_Immutable (F : Entity_Id) return Boolean
   with Pre => Is_Formal (F);
   --  Check if the given formal parameter is immutable, as per the rules
   --  of the SPARK RM section 6.4.2(2).

   function Is_Conservatively_By_Copy_Type (F : Entity_Id) return Boolean
     with Pre => Is_Formal (F) and then Is_Immutable (F);
   --  Check whether the (formal immutable) parameter should be regarded as a
   --  by-copy type for the purposes of aliasing.

   function Is_Anonymous_Access_To_Constant (Typ : Entity_Id) return Boolean is
     (Is_Anonymous_Access_Type (Typ) and then Is_Access_Constant (Typ))
   with Pre => (Is_Type (Typ));
   --  Implement anonymous access-to-constant via the intersection of
   --  'anonymous access' and 'access constant'.

   procedure Check_Node_Against_Node
     (FA       : in out Flow_Analysis_Graphs;
      A, B     : Node_Or_Entity_Id;
      A_Formal : Entity_Id;
      B_Formal : Entity_Id;
      Status   : out Computed_Aliasing_Result)
   with Pre => Is_Formal (A_Formal)
               and then (No (B_Formal) or else Is_Formal (B_Formal));
   --  Checks the two nodes for aliasing and issues an error message if
   --  appropriate. The formal for B can be Empty, in which case we assume it
   --  is a global.

   procedure Update_Status (Status         : in out Computed_Aliasing_Result;
                            Current_Status : Computed_Aliasing_Result);
   --  Updates the aliasing Status only if the Current_Status is worse (in
   --  terms of the ordering given by the type Computed_Aliasing_Result).

   procedure Trace_Line (Txt : String);
   procedure Trace_Two_Nodes (Text1     : String;
                              Node1     : Node_Id;
                              Text2     : String := "";
                              Node2     : Node_Id;
                              Text3     : String := "";
                              Two_Lines : Boolean := False);
   --  Emit debug information if Trace_Antialiasing is True

   ------------------
   -- Check_Ranges --
   ------------------

   function Check_Ranges (Range_A : Node_Id;
                          Range_B : Node_Id)
                          return Non_Obvious_Aliasing_Check_Result
   is
      function LT (A, B : Node_Id) return Boolean;
      --  Return true iff A < B

      function GE (A, B : Node_Id) return Boolean;
      --  Return true iff A >= B

      function Empty (A, B : Node_Id) return Boolean;
      --  Return true iff A > B

      function Full (A, B : Node_Id) return Boolean;
      --  Return true iff A <= B

      --------
      -- LT --
      --------

      function LT (A, B : Node_Id) return Boolean is
        (Compile_Time_Compare (A, B, True) = LT);

      --------
      -- GE --
      --------

      function GE (A, B : Node_Id) return Boolean is
        (Compile_Time_Compare (A, B, True) in GE | GT | EQ);

      -----------
      -- Empty --
      -----------

      function Empty (A, B : Node_Id) return Boolean is
        (Compile_Time_Compare (A, B, True) = GT);

      ----------
      -- Full --
      ----------

      function Full (A, B : Node_Id) return Boolean is
        (Compile_Time_Compare (A, B, True) in LT | LE | EQ);

      Range_Expr_A : constant Node_Id := Get_Range (Range_A);
      Range_Expr_B : constant Node_Id := Get_Range (Range_B);

      AL : constant Node_Id := Low_Bound  (Range_Expr_A);
      AH : constant Node_Id := High_Bound (Range_Expr_A);
      BL : constant Node_Id := Low_Bound  (Range_Expr_B);
      BH : constant Node_Id := High_Bound (Range_Expr_B);

   --  Start of processing for Check_Range

   begin
      if Empty (AL, AH)
        or else Empty (BL, BH)
        or else LT (AH, BL)
        or else LT (BH, AL)
      then
         --  We definitely have different, non-overlapping ranges; or at least
         --  one of them is empty.
         return No_Aliasing;

      elsif Full (AL, AH) and then Full (BL, BH) and then
        ((GE (AH, BL) and then GE (BH, AL))
           or else
         (GE (BH, AL) and then GE (AH, BL)))
      then
         --  We definitely have overlapping, non-empty ranges
         return Definite_Aliasing;

      else
         --  We don't know
         return Possible_Aliasing;
      end if;
   end Check_Ranges;

   --------------
   -- Aliasing --
   --------------

   function Aliasing (A,        B        : Node_Id;
                      Formal_A, Formal_B : Entity_Id)
                      return Computed_Aliasing_Result
   is
      function Is_Interesting (N : Node_Id) return Boolean
      with Pre => Nkind (N) in N_Defining_Identifier | N_Subexpr;
      --  Returns True iff N is interesting from the aliasing point of view.
      --  Only objects appearing as the global parameters and some names
      --  appearing as actual parameters are interesting; other expressions are
      --  not.

      --------------------
      -- Is_Interesting --
      --------------------

      function Is_Interesting (N : Node_Id) return Boolean is
      begin
         case Nkind (N) is

            --  Detect names as described by Ada RM 4.1(2/3)

            when
               --  Direct name
                 N_Identifier
               | N_Expanded_Name
               | N_Defining_Identifier

               --  Explicit dereference is now in SPARK
               | N_Explicit_Dereference

               --  Indexed component and slices
               | N_Indexed_Component
               | N_Slice

               --  Selected components
               | N_Selected_Component

               --  Type conversion
               | N_Qualified_Expression
               | N_Type_Conversion

               | N_Unchecked_Type_Conversion
            =>
               return True;

            --  The only interesting attribute reference is 'Access. However
            --  access-to-object is not yet supported by the borrow checker.

            when N_Attribute_Reference =>
               pragma Assert (Attribute_Name (N) /= Name_Access);
               return False;

            --  Detect calls to instances of unchecked conversion. Other
            --  function calls are not interesting, including those returning
            --  access types, because that kind of aliasing should not be a
            --  concern of flow analysis: either the result is newly allocated,
            --  or it's a borrow/observe and dealt with by the borrow checker.

            when N_Function_Call =>
               return Is_Unchecked_Conversion_Instance (Get_Called_Entity (N));

            --  Character literals, qualified expressions are boring

            --  Generalized reference and indexing are suitably expanded

            --  Everything else must be an expression and is thus not
            --  interesting.

            when others =>
               return False;
         end case;
      end Is_Interesting;

      Is_Root : constant array (Node_Kind) of Boolean :=
        (N_Identifier          => True,
         N_Expanded_Name       => True,
         N_Defining_Identifier => True,
         others                => False);

      function Is_Conversion (N : Node_Id) return Boolean;
      --  Returns True iff N represents an type conversion

      -------------------
      -- Is_Conversion --
      -------------------

      function Is_Conversion (N : Node_Id) return Boolean is
      begin
         case Nkind (N) is
            when N_Qualified_Expression
               | N_Type_Conversion
               | N_Unchecked_Type_Conversion
            =>
               return True;

            when N_Function_Call =>
               return Is_Unchecked_Conversion_Instance (Get_Called_Entity (N));

            when others =>
               return False;
         end case;
      end Is_Conversion;

      function Down_One_Level (N : Node_Id) return Node_Id
      with Pre => Is_Interesting (N)
                  and then not Is_Root (Nkind (N));
      --  Goes down the parse tree by one level. For example:
      --     * R.X.Y       ->  R.X
      --     * R.X         ->  R
      --     * A (12)      ->  A
      --     * Wibble (X)  ->  X

      function Path_To_Root (N : Node_Id) return Node_Lists.List
      with Pre  => Nkind (N) in N_Defining_Identifier | N_Subexpr,
           Post => Path_To_Root'Result.Is_Empty
                     or else
                   Is_Root (Nkind (Path_To_Root'Result.First_Element));
      --  Calls Down_One_Level, prepending the result of each such call to the
      --  returned list, until we find an identifier. For example:
      --    * R.X.Y       ->  [R, R.X, R.X.Y]
      --    * A (12)      ->  A
      --    * Wibble (X)  ->  X
      --  When calling Down_One_Level, we inspect the original version of the
      --  node if it has been inlined-for-proof.
      --  If the parameter names an object, then the result starts with the
      --  root object; otherwise, the returned list is empty.
      --  Up_Ignoring_Conversions is the opposite of this routine.

      function Root_Count (Path : Node_Lists.List) return Natural with Ghost;
      --  Returns the number of root nodes on the path

      function Get_Root_Entity (N : Node_Or_Entity_Id) return Entity_Id
      with Pre  => Is_Root (Nkind (N)),
           Post => Is_Object (Get_Root_Entity'Result);
      --  Returns the entity attached to N, which is either an identifier of an
      --  actual or a defining entity of a global.

      procedure Up_Ignoring_Conversions (L : in out Node_Lists.List)
      with Pre  => Is_Interesting (L.First_Element) and then L.Length > 1,
        Post => Is_Interesting (L.First_Element)
        and then L.Length < L'Old.Length;
      --  Goes up the parse tree; usually only one level but if we find a type
      --  conversion of some kind we keep going.

      --------------------
      -- Down_One_Level --
      --------------------

      function Down_One_Level (N : Node_Id) return Node_Id is
      begin
         case Nkind (N) is
            when N_Explicit_Dereference
               | N_Indexed_Component
               | N_Slice
               | N_Selected_Component
            =>
               return Prefix (N);

            when N_Type_Conversion
               | N_Unchecked_Type_Conversion
               | N_Qualified_Expression
            =>
               return Expression (N);

            when N_Function_Call =>
               return First_Actual (N);

            when others =>
               raise Program_Error;
         end case;
      end Down_One_Level;

      ---------------------
      -- Get_Root_Entity --
      ---------------------

      function Get_Root_Entity (N : Node_Or_Entity_Id) return Entity_Id is
         E : Entity_Id;
      begin
         if Nkind (N) = N_Defining_Identifier then
            return N;
         end if;

         E := Entity (N);

         --  Detect overlay with an Address representation clause

         if Ekind (E) in E_Constant | E_Variable
           and then Present (Ultimate_Overlaid_Entity (E))
         then
            return Ultimate_Overlaid_Entity (E);
         else
            return E;
         end if;
      end Get_Root_Entity;

      ------------------
      -- Path_To_Root --
      ------------------

      function Path_To_Root (N : Node_Id) return Node_Lists.List is
         Path    : Node_Lists.List;
         Context : N_Subexpr_Id;
      begin
         --  If we are dealing with a global parameter, then return a list with
         --  its entity.

         if Nkind (N) = N_Defining_Identifier then
            Path.Prepend (N);
            return Path;
         end if;

         --  Otherwise find the root object of the actual parameter expression

         Context := N;

         loop
            --  The root object will appear as an identifier

            if Nkind (Context) in N_Identifier | N_Expanded_Name then

               --  For objects created by inlining-for-proof switch to their
               --  original expression and continue.

               if Is_Rewrite_Substitution (Context) then
                  Context := Original_Node (Context);

               --  For ordinary objects just prepend them to the result and we
               --  are done.

               else
                  Path.Prepend (Context);
                  return Path;
               end if;

            --  Add name components to the path

            elsif Is_Interesting (Context) then
               Path.Prepend (Context);
               Context := Down_One_Level (Context);

            --  Other subexpressions are not object names, so terminate

            else
               return Node_Lists.Empty_List;
            end if;
         end loop;
      end Path_To_Root;

      ----------------
      -- Root_Count --
      ----------------

      function Root_Count (Path : Node_Lists.List) return Natural is
         Count : Natural := 0;
      begin
         --  If the path represents a global parameter, it will consist of a
         --  single N_Defining_Identifier node.

         if Nkind (Path.First_Element) = N_Defining_Identifier then
            pragma Assert (Path.Length = 1);
            return 1;
         end if;

         --  Otherwise it is a sequence starting from an (expanded) name

         pragma Assert
           (Nkind (Path.First_Element) in N_Identifier | N_Expanded_Name);

         for Node of Path loop
            if Is_Root (Nkind (Node)) then
               Count := Count + 1;
            else
               pragma Assert (Is_Interesting (Node));
            end if;
         end loop;
         return Count;
      end Root_Count;

      -----------------------------
      -- Up_Ignoring_Conversions --
      -----------------------------

      procedure Up_Ignoring_Conversions
        (L : in out Node_Lists.List)
      is
      begin
         loop
            L.Delete_First;
            exit when not Is_Conversion (Original_Node (L.First_Element))
              or else L.Length = 1;
         end loop;
      end Up_Ignoring_Conversions;

      --  Local variables

      List_A, List_B : Node_Lists.List;
      Head_A, Head_B : Node_Id;
      Root_A, Root_B : Entity_Id;

      Definitive_Result : Boolean := True;

   --  Start of processing for Aliasing

   begin
      Trace_Two_Nodes (Text1 => "antialiasing: checking ",
                       Node1 => A,
                       Text2 => " <--> ",
                       Node2 => B);

      --  Check the cases involving two actual parameters, with immutable
      --  and/or anonymous acess constant 'in' formal parameter(s) from the
      --  SPARK RM 6.4.2(3).
      declare
         A_Is_Immutable : constant Boolean :=
           Is_Immutable (Formal_A);
         A_Is_Anonymous_Access_Constant_In : constant Boolean :=
           Ekind (Formal_A) = E_In_Parameter
           and then Is_Anonymous_Access_To_Constant (Etype (Formal_A));
         B_Present_And_Immutable : constant Boolean :=
           Present (Formal_B)
           and then Is_Immutable (Formal_B);
         B_Present_And_Anonymous_Access_Constant_In : constant Boolean :=
           Present (Formal_B)
           and then Ekind (Formal_B) = E_In_Parameter
           and then Is_Anonymous_Access_To_Constant (Etype (Formal_B));
      begin
         --  Determine if two actual parameters are both either immutable or
         --  anonymous access-to-constant "in" parameters.
         if (A_Is_Immutable
             or else A_Is_Anonymous_Access_Constant_In)
           and then (B_Present_And_Immutable
                     or else B_Present_And_Anonymous_Access_Constant_In)
         then
            Trace_Line ("   -> formal parameters A and B are both either " &
                          "immutable or mode 'in' anonymous " &
                          "access-to-constant.");
            return Impossible;

         --  Determine if at least one of the corresponding formal
         --  parameters is immutable and a by-copy type.

         elsif A_Is_Immutable and then Present (Formal_B)
           and then Is_Conservatively_By_Copy_Type (Formal_A)
         then
            Trace_Line ("   -> A does not require aa checking");
            return Impossible;

         elsif B_Present_And_Immutable
           and then Is_Conservatively_By_Copy_Type (Formal_B)
         then
            Trace_Line ("   -> B does not require aa checking");
            return Impossible;

         --  We also want to avoid checking abstract state

         elsif No (Formal_B) and then Ekind (B) = E_Abstract_State then
            Trace_Line ("   -> B is an abstract state");
            return Impossible;
         end if;
      end;

      --  Ok, so both nodes might potentially alias. We now need to work out
      --  the root nodes of each expression.

      List_A := Path_To_Root (A);
      List_B := Path_To_Root (B);

      --  Aliasing requires both parameters to name an object

      if List_A.Is_Empty then
         Trace_Line ("   -> A is not interesting");
         return Impossible;
      elsif List_B.Is_Empty then
         Trace_Line ("   -> B is not interesting");
         return Impossible;
      end if;

      Head_A := List_A.First_Element; --  Root node of A
      Head_B := List_B.First_Element; --  Root node of B

      Trace_Two_Nodes (Text1     => "   -> root of A: ",
                       Node1     => Head_A,
                       Text2     => "   -> root of B: ",
                       Node2     => Head_B,
                       Two_Lines => True);

      pragma Assert (Root_Count (List_A) = 1);
      pragma Assert (Root_Count (List_B) = 1);

      --  A quick sanity check. If the root nodes refer to different entities
      --  then we cannot have aliasing.

      Root_A := Get_Root_Entity (Head_A);
      Root_B := Get_Root_Entity (Head_B);

      if Root_A /= Root_B then
         Trace_Line ("   -> different root entities");
         return Impossible;
      end if;

      --  We now know that the root nodes refer to the same entity

      --  From the SPARK RM 6.4.2(1) an object is 'interfering' if it is
      --  unsynchronised or it is synchronised only due to being constant after
      --  elaboration.

      if Is_Synchronized_Object (Root_A)
        and then (Ekind (Root_A) /= E_Variable
                  or else not Is_Constant_After_Elaboration (Root_A))
      then
         Trace_Line ("   -> non-interfering objects");
         return Impossible;
      end if;

      --  We now need to walk up the tree and see if we differ somehow.
      --  For example, right now we might have:
      --     * A,              A           --  illegal
      --     * A.X.Y (1 .. J), A.X         --  illegal
      --     * A.X,            A.Y         --  OK
      --     * A (J),          A (K)       --  maybe illegal
      --     * A.X,            Wibble (A)  --  illegal
      --     * A,              Wibble (A)  --  illegal
      --  etc.
      --
      --  Also, we know that Is_Root holds for the head elements of List_A and
      --  List_B, which means that we are dealing with an identifier and not an
      --  unchecked conversion, etc.

      Trace_Line ("   -> same root entity");

      while List_A.Length > 1 and then List_B.Length > 1 loop

         --  Go up the tree one level. If we hit an unchecked conversion or
         --  type conversion we 'ignore' it. For example:
         --     * R.X  ->  R.X.Y
         --     * R    ->  Wibble (R).X
         --     * R    ->  Wibble (R)    (if Wibble (R) is the top)

         Up_Ignoring_Conversions (List_A);
         Up_Ignoring_Conversions (List_B);

         Head_A := List_A.First_Element;
         Head_B := List_B.First_Element;
         pragma Assert (not Is_Root (Nkind (Head_A)));
         pragma Assert (not Is_Root (Nkind (Head_B)));

         --  Check if we are dealing with any type conversion *now*. If so, we
         --  have aliasing.

         if Is_Conversion (Head_A) or else Is_Conversion (Head_B) then
            Trace_Line ("   -> identical tree followed by conversion");
            return Definite_Aliasing;
         end if;

         --  We have now gone up one level on each side. We need to check the
         --  two fields.

         if Nkind (Head_A) = Nkind (Head_B) then

            --  We definitely need to check this. Some possibilities:
            --     R.X         <-->  R.X.Y
            --     R.X         <-->  R.Z
            --     A (5)       <-->  A (J).Wibble
            --     A (1 .. 3)  <-->  A (K .. L)

            Trace_Two_Nodes (Text1 => "   -> checking same structure at ",
                             Node1 => Head_A,
                             Text2 => " <--> ",
                             Node2 => Head_B);

            case Nkind (Head_A) is
               when N_Selected_Component =>
                  if Entity (Selector_Name (Head_A)) /=
                     Entity (Selector_Name (Head_B))
                  then
                     Trace_Line ("   -> selectors differ");
                     return No_Aliasing;
                  end if;

               when N_Indexed_Component =>
                  declare
                     Index_A : Node_Id := First (Expressions (Head_A));
                     Index_B : Node_Id := First (Expressions (Head_B));
                  begin
                     while Present (Index_A) loop
                        pragma Assert (Present (Index_B));

                        case Compile_Time_Compare (Index_A, Index_B, True) is
                           when LT | GT | NE =>
                              Trace_Two_Nodes
                                (Text1 => "   -> index ",
                                 Node1 => Index_A,
                                 Text2 => " and ",
                                 Node2 => Index_B,
                                 Text3 => " statically differ");
                              return No_Aliasing;

                           when EQ =>
                              null;

                           when LE | GE | Unknown =>
                              Definitive_Result := False;
                        end case;

                        Next (Index_A);
                        Next (Index_B);
                     end loop;
                  end;

               when N_Slice =>
                  case Check_Ranges (Discrete_Range (Head_A),
                                     Discrete_Range (Head_B)) is
                     when No_Aliasing =>
                        Trace_Two_Nodes
                          (Text1 => "   -> slice ",
                           Node1 => Discrete_Range (Head_A),
                           Text2 => " and ",
                           Node2 => Discrete_Range (Head_B),
                           Text3 => " statically distinct");
                        return No_Aliasing;

                     when Definite_Aliasing =>
                        null;

                     when Possible_Aliasing =>
                        Definitive_Result := False;
                  end case;

               when N_Explicit_Dereference =>
                  null;

               when others =>
                  raise Why.Unexpected_Node;
            end case;

         elsif (Nkind (Head_A) = N_Slice and then
                  Nkind (Head_B) = N_Indexed_Component) or else
           (Nkind (Head_A) = N_Indexed_Component and then
              Nkind (Head_B) = N_Slice)
         then

            --  We also need to check this. One possibility:
            --     A (1 .. 3)  <-->  A (J)

            --  If the user *really* wants this we can implement it. For now
            --  skip this as its potentially quite hard as we need to sync up
            --  with the other expression.
            --
            --  Consider this: A (4 .. 10) (5 .. 8) (3)

            Trace_Line ("   -> slice v.s. index is difficult - bailing out");

            return Possible_Aliasing;

         else

            --  We have previously established that things might possibly
            --  alias, which means the tree should have been similar enough.
            --  Look for the bug in the above code.

            raise Why.Unexpected_Node;
         end if;

      end loop;

      --  The tree so far was exactly the same, so A and B definitely alias

      Trace_Line ("   -> identical tree so far, hit end");
      if Definitive_Result then
         Trace_Line ("   -> result is definitive");
      end if;

      if Definitive_Result then
         return Definite_Aliasing;
      else
         return Possible_Aliasing;
      end if;
   end Aliasing;

   ------------------
   -- Is_Immutable --
   ------------------

   function Is_Immutable (F : Entity_Id) return Boolean is
      Typ : constant Entity_Id := Etype (F);
   begin
      return
        --  Immutable formal parameters are of mode 'in' and neither of an
        --  access-to-variable type, nor of an anonymous access-to-constant
        --  type.
        Ekind (F) = E_In_Parameter
        and then not Is_Access_Variable (Typ)
        and then not Is_Anonymous_Access_To_Constant (Typ);
   end Is_Immutable;

   ------------------------------------
   -- Is_Conservatively_By_Copy_Type --
   ------------------------------------

   function Is_Conservatively_By_Copy_Type (F : Entity_Id) return Boolean is
      Typ : constant Entity_Id := Etype (F);
   begin
      return
        --  We need to take a somewhat conservative approach, as anonymous
        --  access-to-constant parameters are strictly pass-by-copy but
        --  actually copy a reference and thus need to be treated more like
        --  pass-by-reference. See notes of SPARK LRM 6.4.2(3).
        Is_By_Copy_Type (Typ)
        and then not Is_Anonymous_Access_To_Constant (Typ);
   end Is_Conservatively_By_Copy_Type;

   -----------------------------
   -- Check_Node_Against_Node --
   -----------------------------

   procedure Check_Node_Against_Node
     (FA       : in out Flow_Analysis_Graphs;
      A, B     : Node_Or_Entity_Id;
      A_Formal : Entity_Id;
      B_Formal : Entity_Id;
      Status   : out Computed_Aliasing_Result)
   is
      Msg    : Unbounded_String := Null_Unbounded_String;
      B_Node : Node_Id;
   begin
      Status := Aliasing (A, B, A_Formal, B_Formal);

      case Status is
         when Impossible =>
            return;

         when Possible_Aliasing
            | Definite_Aliasing
         =>
            null;

         when No_Aliasing =>
            Append (Msg, "non-aliasing of ");
      end case;

      Append (Msg, "formal parameter");
      if Present (B_Formal) then
         Append (Msg, "s & and &");
         B_Node := B_Formal;
      else
         --  ??? maybe have a special message for generated globals
         Append (Msg, " & and global &");
         B_Node := B;
      end if;

      Append
        (Msg,
         (case Status is
             when No_Aliasing       => " proved",
             when Possible_Aliasing => " might be aliased",
             when Definite_Aliasing => " are aliased",
             when Impossible        => raise Program_Error));

      Error_Msg_Flow (FA       => FA,
                      Msg      => To_String (Msg),
                      Severity =>
                        (case Status is
                         when No_Aliasing       => Info_Kind,
                         when Possible_Aliasing => Medium_Check_Kind,
                         when Definite_Aliasing => High_Check_Kind,
                         when Impossible        => raise Program_Error),
                      N        => A,
                      F1       => Direct_Mapping_Id (A_Formal),
                      F2       => Direct_Mapping_Id (B_Node),
                      Tag      => Aliasing,
                      SRM_Ref  => (if Status = No_Aliasing
                                   then ""
                                   else "6.4.2"));
   end Check_Node_Against_Node;

   --------------------------
   -- Check_Procedure_Call --
   --------------------------

   procedure Check_Procedure_Call
     (FA : in out Flow_Analysis_Graphs;
      N  : Node_Id)
   is
      procedure Check_Parameter (Formal : Entity_Id; Actual : Node_Id);
      --  Check parameters against other parameters and globals.

      procedure Check_Aliasing_In_Call is new
        Iterate_Call_Parameters (Check_Parameter);
      --  The general idea here is to make sure none of the globals and
      --  parameters overlap. If we have a procedure with parameters X, Y and
      --  Z and globals A and B, then we check the following:
      --
      --     X v.s. (Y, Z, A, B)
      --     Y v.s. (   Z, A, B)
      --     Z v.s. (      A, B)
      --
      --  In particular we do not check the globals against each other and we
      --  do not check combinations of parameters which we have already seen.
      --  This is implemented by this procedure having the same loop as
      --  Check_Parameter_Against_Parameters_And_Globals and by only checking
      --  parameters once we have seen our parameter we compare against.

      function Visible_Globals (FS : Flow_Id_Sets.Set) return Node_Sets.Set
      with Post => (for all E of Visible_Globals'Result =>
                       Is_Global_Entity (E)
                         or else
                       (Ekind (E) = E_Constant
                        and then not Has_Variable_Input (E)));
      --  Returns the subset of FS that is represented by Entity_Ids, which are
      --  globals except when a constant without variable input wrongly appears
      --  in a user-written contract.

      Writes_Or_Reads : Node_Sets.Set;
      --  Global outputs and in_outs. For aliasing these behave as OUT and
      --  IN_OUT formal parameters, respectively.

      Reads_Only      : Node_Sets.Set;
      --  Global inputs and proof_ins (which for aliasing behave as immutable
      --  IN formal parameters). Note that global access types are never
      --  regarded as purely mode "in" (unlike the similar case for formal
      --  parameters) so are never members of this set.

      Current_Status : Computed_Aliasing_Result;
      Status         : Computed_Aliasing_Result := Impossible;

      ---------------------
      -- Check_Parameter --
      ---------------------

      procedure Check_Parameter (Formal : Entity_Id; Actual : Node_Id) is
         Formal_Is_Immutable : constant Boolean := Is_Immutable (Formal);

         Other_Formal : Entity_Id := Next_Formal (Formal);
         Other_Actual : Node_Id   := Next_Actual (Actual);
         --  Formal/Actual will be checked against formals/actuals that follow
         --  them; this way we check each pair of them exactly once.

      begin
         while Present (Other_Formal) loop
            pragma Assert (Present (Other_Actual));

            Check_Node_Against_Node
              (FA       => FA,
               A        => Actual,
               B        => Other_Actual,
               A_Formal => Formal,
               B_Formal => Other_Formal,
               Status   => Current_Status);

            Update_Status (Status, Current_Status);

            Next_Formal (Other_Formal);
            Next_Actual (Other_Actual);
         end loop;

         pragma Assert (No (Other_Actual));

         --  The rules of SPARK RM 6.4.2(4) are such that we can split the
         --  cases handling read-only globals separately from Output + In_Out
         --  globals.
         --  If a global item is read-only, there cannot be aliasing between it
         --  and the corresponding formal parameter if the latter is either
         --  * immutable; or
         --  * of mode "in" and anonymous access-to-constant type.
         if Formal_Is_Immutable
           or else (Ekind (Formal) = E_In_Parameter
                    and then Is_Anonymous_Access_To_Constant (Etype (Formal)))
         then
            if not Reads_Only.Is_Empty then
               Trace_Line ("   -> A does not require aa checking against " &
                             "read-only globals");
            end if;
         else
            for G of Reads_Only loop
               Check_Node_Against_Node
                 (FA       => FA,
                  A        => Actual,
                  B        => G,
                  A_Formal => Formal,
                  B_Formal => Empty,
                  Status   => Current_Status);

               Update_Status (Status, Current_Status);
            end loop;
         end if;

         --  From SPARK RM 6.4.2(4):
         --  * If the global item's mode is Output or In_Out, then the
         --    corresponding formal parameter shall be immutable and of a
         --    by-copy type.
         if Formal_Is_Immutable
           and then Is_Conservatively_By_Copy_Type (Formal)
         then
            if not Writes_Or_Reads.Is_Empty then
               Trace_Line ("   -> A does not require aa checking against " &
                             "OUT or IN_OUT globals");
            end if;
         else
            for G of Writes_Or_Reads loop
               Check_Node_Against_Node
                 (FA       => FA,
                  A        => Actual,
                  B        => G,
                  A_Formal => Formal,
                  B_Formal => Empty,
                  Status   => Current_Status);

               Update_Status (Status, Current_Status);
            end loop;
         end if;
      end Check_Parameter;

      ---------------------
      -- Visible_Globals --
      ---------------------

      function Visible_Globals (FS : Flow_Id_Sets.Set) return Node_Sets.Set
      is
         Results : Node_Sets.Set;
      begin
         for F of FS loop
            case F.Kind is
               when Direct_Mapping =>
                  Results.Insert (Get_Direct_Mapping_Id (F));

                  --  If we don't have an Entity_Id for a global, then it can't
                  --  be referenced as a parameter.

               when Magic_String =>
                  null;

               when others =>
                  raise Program_Error;
            end case;
         end loop;

         return Results;
      end Visible_Globals;

      --  Local variables

      Called_Thing : constant Entity_Id := Get_Called_Entity (N);

      Globals : Global_Flow_Ids;

      use type Node_Sets.Set;

   --  Start of processing for Check_Procedure_Call

   begin
      if Ekind (Called_Thing) /= E_Subprogram_Type then
         Get_Globals (Subprogram => Called_Thing,
                      Scope      => FA.B_Scope,
                      Classwide  => Flow_Classwide.Is_Dispatching_Call (N),
                      Globals    => Globals);
      end if;

      Writes_Or_Reads := Visible_Globals (Globals.Outputs);
      Reads_Only      :=
        (Visible_Globals (Globals.Inputs) - Writes_Or_Reads) or
          Visible_Globals (Globals.Proof_Ins);

      --  Check formal parameters against other parameters and globals

      Check_Aliasing_In_Call (N);

      Aliasing_Status.Insert (N, Status);

      --  ??? Need to check for aliasing between abstract state and computed
      --  globals.

   end Check_Procedure_Call;

   -----------------------------------
   -- Get_Aliasing_Status_For_Proof --
   -----------------------------------

   function Get_Aliasing_Status_For_Proof (N : Node_Id)
                                           return Aliasing_Check_Result
   is
      C : constant Aliasing_Statuses.Cursor := Aliasing_Status.Find (N);
   begin
      return (if Aliasing_Statuses.Has_Element (C)
              then Aliasing_Status (C)
              else Unchecked);
   end Get_Aliasing_Status_For_Proof;

   -------------------
   -- Update_Status --
   -------------------

   procedure Update_Status (Status         : in out Computed_Aliasing_Result;
                            Current_Status : Computed_Aliasing_Result)
   is
   begin
      if Current_Status > Status then
         Status := Current_Status;
      end if;
   end Update_Status;

   --  Debug routines, localised to declutter code coverage analysis
   pragma Annotate (Xcov, Exempt_On, "Compilation-dependent debug code");
   ----------------
   -- Trace_Line --
   ----------------

   procedure Trace_Line (Txt : String)
   is
   begin
      if Trace_Antialiasing then
         Write_Line (Txt);
      end if;
   end Trace_Line;

   ---------------------
   -- Trace_Two_Nodes --
   ---------------------

   procedure Trace_Two_Nodes (Text1     : String;
                              Node1     : Node_Id;
                              Text2     : String := "";
                              Node2     : Node_Id;
                              Text3     : String := "";
                              Two_Lines : Boolean := False)
   is
   begin
      if Trace_Antialiasing then
         Write_Str (Text1);
         Sprint_Node (Node1);
         if Two_Lines then
            Write_Eol;
         end if;
         Write_Str (Text2);
         Sprint_Node (Node2);
         Write_Str (Text3);
         Write_Eol;
      end if;
   end Trace_Two_Nodes;
   pragma Annotate (Xcov, Exempt_Off);

end Flow.Analysis.Antialiasing;
