------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--               G N A T 2 W H Y - E X P R - A G G R E G A T E S            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2023-2023, AdaCore                     --
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

with Ada.Containers.Hashed_Maps;
with Ada.Containers.Indefinite_Vectors;
with Ada.Text_IO;
with Ada.Unchecked_Deallocation;
with Elists;              use Elists;
with Gnat2Why.Tables;     use Gnat2Why.Tables;
with GNAT.Source_Info;
with GNATCOLL.Symbols;    use GNATCOLL.Symbols;
with Sinput;              use Sinput;
with SPARK_Definition;    use SPARK_Definition;
with String_Utils;        use String_Utils;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Modules;   use Why.Atree.Modules;
with Why.Gen.Arrays;      use Why.Gen.Arrays;
with Why.Gen.Binders;     use Why.Gen.Binders;
with Why.Gen.Decl;        use Why.Gen.Decl;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Progs;       use Why.Gen.Progs;
with Why.Gen.Records;     use Why.Gen.Records;
with Why.Images;          use Why.Images;

package body Gnat2Why.Expr.Aggregates is

   package Association_Trees is

   --  This package defines the tree structure which is used to aggregate the
   --  associations inside deep delta aggregates. The structure is used as a
   --  pattern for the structure of the base expression. It is extended on
   --  demands depending on the (record) subcomponents which are effectively
   --  mentioned in selectors. For array components, as the index values might
   --  not be statically known, a single branch is created.
   --
   --  The component associations in the aggregate are inserted in the tree
   --  in the following manner. Each node in the tree contains a sequence of
   --  "constrained values", one per association, always in the same order.
   --  These constrained values contain an array of "choices", which are
   --  basically concrete values for the array indexes that occur in the
   --  prefix of the selector, and a status. The status can be "preserved",
   --  "partial", if the association updates a subcomponent of the prefix,
   --  or "entire" with an associated value. The last case corresponds to a
   --  write. If the tree has several branches after a write - e.g. .F is
   --  written with the value V, but the tree mentions .F.G - then the write is
   --  propagated to the subtree - .F.G is entirely written with the value V.G.
   --
   --  As an example, consider the following deep delta aggregate:
   --
   --    (... with delta F (I).G => V,
   --                    H => W,
   --                    F (J).G.E => X)
   --
   --  Here are the association stored in its update tree:
   --
   --  Values => ([], PARTIAL), ([], PARTIAL), ([], PARTIAL)
   --  Fields =>
   --     F =>
   --        Values  => ([], PARTIAL), ([], PRESERVED), ([], PARTIAL)
   --        Content =>
   --            Values => ([I], PARTIAL), ([.], PRESERVED), ([J], PARTIAL)
   --            Fields =>
   --               G =>
   --                  Values => ([I], ENTIRE: V), .., ([J], PARTIAL)
   --                  Fields =>
   --                     E =>
   --                       Values => ([I], ENTIRE: V.E), .., ([J], ENTIRE: X)
   --     H =>
   --        Values => ([], PRESERVED), ([], ENTIRE: W), ([], PRESERVED)

      type Path_Kind is (Root, Record_Acc, Array_Acc);

      type Path_Link (Kind : Path_Kind);

      type Opt_Path_Type is access Path_Link;

      subtype Path_Type is not null Opt_Path_Type;

      type Path_Link (Kind : Path_Kind) is record
         case Kind is
            when Root =>
               Expr   : N_Subexpr_Id;
            when Record_Acc | Array_Acc =>
               Prefix : Path_Type;
               case Kind is
                  when Root =>
                     null;
                  when Record_Acc =>
                     Field : Entity_Id;
                  when Array_Acc =>
                     Index : Positive;
               end case;
         end case;
      end record;
      --  Paths are used to represent the value of propagated writes, like
      --  V.E above. A path is either a root with an expression (V) or a
      --  record or array access in a prefix.

      type Write_Kind is (Preserved, Partial, Entire);

      type Write_Type (Kind : Write_Kind := Preserved) is record
         case Kind is
            when Entire =>
               Path : Path_Type;
            when others =>
               null;
         end case;
      end record;
      --  Writes are used for the status of constrained values. They can either
      --  be the special values Preserved and Partial, or Entire with a value
      --  given as a path.

      type Choice_Array is array (Positive range <>) of Node_Id;

      type Constrained_Value (Size : Natural) is record
         Ada_Node : Node_Id;
         Status   : Write_Type;
         Choices  : Choice_Array (1 .. Size);
      end record;
      --  Constrained values contain a sequence of choices giving concrete
      --  values as Ada nodes (if any, Empty otherwise) for the indexes in the
      --  prefix and a status to represent the write. They contain also an
      --  Ada_Node which can be used to locate checks on writes (either record
      --  or array accesses or predicate checks).

      package Constrained_Value_Vectors is new
        Ada.Containers.Indefinite_Vectors (Positive, Constrained_Value);

      type Tree_Kind is (Entire_Object, Record_Components, Array_Components);

      type Write_Status;
      type Write_Status_Access is access Write_Status;

      package Write_Status_Maps is new Ada.Containers.Hashed_Maps
        (Key_Type        => Node_Id,
         Element_Type    => Write_Status_Access,
         Hash            => Common_Containers.Node_Hash,
         Equivalent_Keys => "=");

      type Write_Status (Kind : Tree_Kind) is limited record
         Ty     : Entity_Id;
         Values : Constrained_Value_Vectors.Vector;
         case Kind is
            when Entire_Object     =>
               null;
            when Record_Components =>
               Component_Status : Write_Status_Maps.Map;
            when Array_Components  =>
               Content_Status   : Write_Status_Access;
         end case;
      end record;
      --  The tree represents the structure of the base expression in the delta
      --  aggregate. It is extended (or unfolded) on demand so that subtrees
      --  correspond to subcomponents which are mentionned in the delta
      --  aggregate.
      --  A tree or subtree can be either a leaf of kind Entire_Object (for
      --  subcomponents which are either not composite or still folded), a
      --  (partially) unfolded record, containing a subtree for each component
      --  mentioned in the aggregate, or an unfolded array containing a
      --  subtree for all its components grouped together.
      --  Each node of the tree contains a sequence of constrained values, one
      --  per association in the delta aggregate. The choices in the
      --  constrained values give only the index values in the prefix, so the
      --  values of the Content_Status subtree of an unfolded array write
      --  status will contain an additional choice compared to the values of
      --  the array. The choice will be empty for preserved and propagated
      --  values (all indexes are preserved/updated).

      ------------------------------------
      -- Handling of Write_Status Trees --
      ------------------------------------

      procedure Create
        (Ty     : Entity_Id;
         Writes : out Write_Status_Access)
        with Post => Writes /= null;
      --  Allocate a write status for the composite type Ty

      procedure Finalize (Writes : in out Write_Status_Access) with
        Pre => Writes /= null;
      --  Deallocate a write status

      procedure Insert_Association
        (Writes      : not null Write_Status_Access;
         Deep_Access : Node_Id;
         Value       : N_Subexpr_Id);
      --  Insert a new association Deep_Access => Value in Writes

      procedure Print_Writes (Writes  : Write_Status);
      pragma Unreferenced (Print_Writes);
      --  For debugging purposes

   end Association_Trees;
   use Association_Trees;

   -----------------------
   -- Local Subprograms --
   -----------------------

   function Get_Name_For_Aggregate (Expr : Node_Id) return String;
   --  Return a suitable name for the aggregate Expr. If Expr is the
   --  initialization expression in an object declaration, then use the name of
   --  the object as basis, which ensures stable naming across changes in
   --  GNATprove. Otherwise, use a temporary name based on a counter.

   -----------------------
   -- Association_Trees --
   -----------------------

   package body Association_Trees is

      -----------------------
      -- Local Subprograms --
      -----------------------

      procedure Free is new Ada.Unchecked_Deallocation
        (Path_Link, Opt_Path_Type);
      procedure Free is new Ada.Unchecked_Deallocation
        (Write_Status, Write_Status_Access);

      --  Constructors for writes

      function Partial_Write return Write_Type is
        (Write_Type'(Kind => Partial));
      --  PARTIAL

      function Discard_Write return Write_Type is
        (Write_Type'(Kind => Preserved));
      --  PRESERVED

      function New_Write (Expr : N_Subexpr_Id) return Write_Type is
        (Write_Type'(Entire, new Path_Link'(Kind => Root, Expr => Expr)));
      --  ENTIRE: Expr

      function Record_Access
        (Prefix : Write_Type;
         Field  : Entity_Id) return Write_Type
      is
        (case Prefix.Kind is
            when Partial   => raise Program_Error,
            when Preserved => Prefix,
            when Entire    =>
           (Entire, new Path_Link'
                (Kind => Record_Acc, Prefix => Prefix.Path, Field => Field)));
      --  Generate ENTIRE: Prefix.Field if Prefix is of entirely updated and
      --  PRESERVED if it is preserved.

      function Array_Access
        (Prefix : Write_Type;
         Index  : Positive) return Write_Type
      is
        (case Prefix.Kind is
            when Partial   => raise Program_Error,
            when Preserved => Prefix,
            when Entire    =>
           (Entire, new Path_Link'
                (Kind => Array_Acc, Prefix => Prefix.Path, Index => Index)));
      --  Generate ENTIRE: Prefix (Index) if Prefix is of entirely updated and
      --  PRESERVED if it is preserved.

      procedure Insert_Array_Association
        (Writes       : not null Write_Status_Access;
         Ada_Node     : Node_Id;
         Choice       : Node_Id;
         Status       : Write_Type;
         Unfold       : Boolean;
         Local_Writes : out not null Write_Status_Access)
        with
          Pre  => Writes.Kind = Array_Components,
          Post => Local_Writes.Values.Last_Element.Status = Status
          and then (if Unfold then Local_Writes.Kind /= Entire_Object);
      --  Extend the last branch of Writes with an update to an array component
      --  indexed by Choice with the status Status. Local_Writes is set to the
      --  subtree of Writes for array components after the call.
      --  If Unfold is True, also unfold Local_Writes so it can be further
      --  extended.

      procedure Insert_Record_Association
        (Writes       : not null Write_Status_Access;
         Ada_Node     : Node_Id;
         Field        : Entity_Id;
         Status       : Write_Type;
         Unfold       : Boolean;
         Local_Writes : out not null Write_Status_Access)
        with
          Pre  => Writes.Kind = Record_Components,
          Post => Local_Writes.Values.Last_Element.Status = Status
          and then (if Unfold then Local_Writes.Kind /= Entire_Object);
      --  Add a constrained value with the choices of the last value of Writes
      --  and the status Status to the subtree associated to a record component
      --  Field in Writes. Also propagate the last constrained value of Writes
      --  to the potential other components of Writes.
      --  Local_Writes is set to the subtree of Writes associated to Field
      --  after the call.
      --  If Unfold is True, also unfold Local_Writes so it can be further
      --  extended.

      procedure Propagate
        (Writes    : not null Write_Status_Access;
         Choices   : Choice_Array;
         Status    : Write_Type;
         Skip_Root : Boolean := False)
        with Pre => Status.Kind /= Partial;
      --  Propagate constrained value (Choices, Status) to subtrees of Writes.
      --  If Skip_Root is True, do not add the constrained value to the root of
      --  the tree.

      procedure Insert_Association_Internal
        (Writes       : not null Write_Status_Access;
         Deep_Access  : Node_Id;
         Status       : Write_Type;
         Unfold       : Boolean;
         Local_Writes : out not null Write_Status_Access)
        with
          Pre  => Status.Kind /= Preserved,
          Post => Local_Writes.Values.Last_Element.Status = Status
          and then (if Unfold then Local_Writes.Kind /= Entire_Object);
      --  Create a branch for an association Deep_Access => Status in Writes.
      --  PARTIAL is associated to prefixes of Deep_Access and PRESERVED is
      --  propagated to their siblings. Local_Writes is set to the subtree of
      --  Writes associated to Deep_Access after the call. Only the root of
      --  Local_Writes has been updated with Value. It has not been propagated
      --  to its subtrees. If Unfold is True, also unfold Local_Writes so it
      --  can be further extended.

      procedure Unfold_Tree (Writes : in out not null Write_Status_Access);
      --  Unfold a folded subtree depending on its type

      ------------
      -- Create --
      ------------

      procedure Create
        (Ty     : Entity_Id;
         Writes : out Write_Status_Access)
      is
      begin
         Writes := new
           Write_Status'(Kind   => Entire_Object,
                         Ty     => Retysp (Ty),
                         Values => Constrained_Value_Vectors.Empty);
         Unfold_Tree (Writes);
      end Create;

      --------------
      -- Finalize --
      --------------

      procedure Finalize (Writes : in out Write_Status_Access) is
      begin
         for Value of Writes.Values loop
            if Value.Status.Kind = Entire then
               declare
                  P : Opt_Path_Type := Value.Status.Path;
               begin
                  Free (P);
                  pragma Annotate (CodePeer, False_Positive, "use after free",
                                   "Path is only freed through one owner");
               end;
            end if;
         end loop;

         case Writes.Kind is
            when Entire_Object =>
               null;
            when Record_Components =>
               for Comp_Writes of Writes.Component_Status loop
                  Finalize (Comp_Writes);
               end loop;
            when Array_Components =>
               Finalize (Writes.Content_Status);
         end case;
         Free (Writes);
      end Finalize;

      ------------------------------
      -- Insert_Array_Association --
      ------------------------------

      procedure Insert_Array_Association
        (Writes       : not null Write_Status_Access;
         Ada_Node     : Node_Id;
         Choice       : Node_Id;
         Status       : Write_Type;
         Unfold       : Boolean;
         Local_Writes : out not null Write_Status_Access)
      is
      begin
         --  Unfold the content tree if necessary

         if Unfold then
            Unfold_Tree (Writes.Content_Status);
         end if;

         Local_Writes := Writes.Content_Status;

         --  Insert the new value. Its choice array is obtained by appending
         --  Choice to the last choices of Writes.

         declare
            Choices : constant Choice_Array :=
              Writes.Values.Last_Element.Choices;
         begin
            Local_Writes.Values.Append
              (Constrained_Value'
                 (Size     => Choices'Length + 1,
                  Ada_Node => Ada_Node,
                  Status   => Status,
                  Choices  => Choices & Choice));
         end;
      end Insert_Array_Association;

      ------------------------
      -- Insert_Association --
      ------------------------

      procedure Insert_Association
        (Writes      : not null Write_Status_Access;
         Deep_Access : Node_Id;
         Value       : N_Subexpr_Id)
      is
         Local_Writes : Write_Status_Access;

      begin
         --  Create a branch for the new association

         Insert_Association_Internal
           (Writes       => Writes,
            Deep_Access  => Deep_Access,
            Status       => New_Write (Value),
            Unfold       => False,
            Local_Writes => Local_Writes);

         --  Propagate the new value in the corresponding subtree

         Propagate
           (Writes    => Local_Writes,
            Choices   => Local_Writes.Values.Last_Element.Choices,
            Status    => Local_Writes.Values.Last_Element.Status,
            Skip_Root => True);
      end Insert_Association;

      ---------------------------------
      -- Insert_Association_Internal --
      ---------------------------------

      procedure Insert_Association_Internal
        (Writes       : not null Write_Status_Access;
         Deep_Access  : Node_Id;
         Status       : Write_Type;
         Unfold       : Boolean;
         Local_Writes : out not null Write_Status_Access)
      is
         Prefix_Writes : Write_Status_Access;
      begin
         --  Create a branch for the new association. Prefixes of Deep_Access
         --  are partially updated. Siblings are preserved.

         if Is_Root_Prefix_Of_Deep_Choice (Deep_Access) then

            --  The root has been reached. Insert a new branch for the new
            --  association. It is partially written.

            Writes.Values.Append
              (Constrained_Value'
                 (Size     => 0,
                  Ada_Node => Deep_Access,
                  Status   => Partial_Write,
                  Choices  => (1 .. 0 => <>)));
            Prefix_Writes := Writes;

            --  Insert the last association

            if Has_Array_Type (Writes.Ty) then
               Insert_Array_Association
                 (Writes       => Prefix_Writes,
                  Ada_Node     => Deep_Access,
                  Choice       => Deep_Access,
                  Status       => Status,
                  Unfold       => Unfold,
                  Local_Writes => Local_Writes);

            else
               pragma Assert
                 (Nkind (Deep_Access) in N_Identifier | N_Expanded_Name);

               declare
                  Sel_Ent : constant Entity_Id :=
                    Entity (Deep_Access);
                  Field   : constant Entity_Id :=
                    Search_Component_In_Type (Prefix_Writes.Ty, Sel_Ent);
                  pragma Assert (Present (Field));

               begin
                  Insert_Record_Association
                    (Writes       => Prefix_Writes,
                     Ada_Node     => Deep_Access,
                     Field        => Field,
                     Status       => Status,
                     Unfold       => Unfold,
                     Local_Writes => Local_Writes);
               end;
            end if;
         else

            --  Create a branch for the prefix. It is partially written.
            --  Unfold it so it can be expanded.

            Insert_Association_Internal
              (Writes       => Writes,
               Deep_Access  => Prefix (Deep_Access),
               Status       => Partial_Write,
               Unfold       => True,
               Local_Writes => Prefix_Writes);

            --  Insert the last association

            case Nkind (Deep_Access) is
               when N_Indexed_Component =>
                  declare
                     Index_Value : constant Node_Id :=
                       First (Expressions (Deep_Access));
                     pragma Assert (No (Next (Index_Value)));

                  begin
                     Insert_Array_Association
                       (Writes       => Prefix_Writes,
                        Ada_Node     => Deep_Access,
                        Choice       => Index_Value,
                        Status       => Status,
                        Unfold       => Unfold,
                        Local_Writes => Local_Writes);
                  end;

               when N_Selected_Component =>
                  declare
                     Sel_Ent : constant Entity_Id :=
                       Entity (Selector_Name (Deep_Access));
                     Field   : constant Entity_Id :=
                       Search_Component_In_Type (Prefix_Writes.Ty, Sel_Ent);
                     pragma Assert (Present (Field));

                  begin
                     Insert_Record_Association
                       (Writes       => Prefix_Writes,
                        Ada_Node     => Deep_Access,
                        Field        => Field,
                        Status       => Status,
                        Unfold       => Unfold,
                        Local_Writes => Local_Writes);
                  end;

               when others =>
                  raise Program_Error;
            end case;
         end if;
      end Insert_Association_Internal;

      -------------------------------
      -- Insert_Record_Association --
      -------------------------------

      procedure Insert_Record_Association
        (Writes       : not null Write_Status_Access;
         Ada_Node     : Node_Id;
         Field        : Entity_Id;
         Status       : Write_Type;
         Unfold       : Boolean;
         Local_Writes : out not null Write_Status_Access)
      is
         use Write_Status_Maps;
         Choices  : constant Choice_Array :=
           Writes.Values.Last_Element.Choices;
         Inserted : Boolean;
         Position : Write_Status_Maps.Cursor;
         use Constrained_Value_Vectors;

      begin
         --  Unfold the subtree if necessary, that is, insert a status for
         --  Field if there is none.

         Writes.Component_Status.Insert (Field, null, Position, Inserted);

         if Inserted then

            --  To initialize its constrained values, use the values of
            --  Writes. Delete the last element, as it will be inserted
            --  afterward specifically.

            declare
               Values : Constrained_Value_Vectors.Vector;
            begin
               for I in 1 .. Writes.Values.Last_Index - 1 loop

                  --  For partially updated values, the new field is preserved

                  if Writes.Values.Element (I).Status.Kind = Partial then
                     Values.Append
                       (New_Item => Constrained_Value'
                          (Size     => Writes.Values.Element (I).Size,
                           Status   => Discard_Write,
                           Ada_Node => Types.Empty,
                           Choices  => Writes.Values.Element (I).Choices));

                  --  Fields of entirely written values are entirely written

                  else
                     Values.Append
                       (New_Item => Constrained_Value'
                          (Size     => Writes.Values.Element (I).Size,
                           Status   => Record_Access
                             (Writes.Values.Element (I).Status, Field),
                           Ada_Node => Writes.Values.Element (I).Ada_Node,
                           Choices  => Writes.Values.Element (I).Choices));
                  end if;
               end loop;

               Writes.Component_Status (Position) := new Write_Status'
                 (Kind   => Entire_Object,
                  Ty     => Retysp (Etype (Field)),
                  Values => Values);
            end;
         end if;

         --  Unfold the component's tree if necessary

         if Unfold then
            Unfold_Tree (Writes.Component_Status (Position));
         end if;

         --  Local_Writes is the status associated to Field in Writes

         Local_Writes := Writes.Component_Status (Position);

         --  Insert the new value. Its choice array is the last choices of
         --  Writes.

         declare
            C_Value : constant Constrained_Value :=
              (Size     => Choices'Length,
               Ada_Node => Ada_Node,
               Status   => Status,
               Choices  => Choices);
         begin
            Local_Writes.Values.Append (New_Item => C_Value);
         end;

         --  Discard the last choices in siblings of Field if any

         for Other_Position in Writes.Component_Status.Iterate loop
            if Other_Position /= Position then
               Propagate
                 (Writes  => Writes.Component_Status (Other_Position),
                  Choices => Choices,
                  Status  => Discard_Write);
            end if;
         end loop;
      end Insert_Record_Association;

      ------------------
      -- Print_Writes --
      ------------------

      pragma Annotate (Xcov, Exempt_On, "Debug code");
      procedure Print_Writes (Writes : Write_Status) is

         procedure Print_Writes
           (Writes  : Write_Status;
            Padding : Natural);
         --  Recursive version, takes an additional parameter for padding

         ------------------
         -- Print_Writes --
         ------------------

         procedure Print_Writes
           (Writes  : Write_Status;
            Padding : Natural)
         is
            Spaces : constant String := (1 .. Padding => ' ');
         begin
            Ada.Text_IO.Put_Line
              (Spaces & "Ty      => " & Source_Name (Writes.Ty));
            Ada.Text_IO.Put (Spaces & "Values  =>");
            for I in 1 .. Writes.Values.Last_Index loop
               Ada.Text_IO.Put (" (");
               if Writes.Values.Element (I).Size = 0 then
                  Ada.Text_IO.Put ("[]");
               else
                  Ada.Text_IO.Put ("[");
                  for K in 1 .. Writes.Values.Element (I).Size loop
                     if No (Writes.Values.Element (I).Choices (K)) then
                        Ada.Text_IO.Put (".");
                     elsif Nkind (Writes.Values.Element (I).Choices (K)) in
                       N_Expanded_Name | N_Identifier
                     then
                        Ada.Text_IO.Put
                          (Source_Name
                             (Entity (Writes.Values.Element (I).Choices (K))));
                     else
                        Ada.Text_IO.Put
                          (Writes.Values.Element (I).Choices (K)'Image);
                     end if;
                     if K /= Writes.Values.Element (I).Size then
                        Ada.Text_IO.Put (", ");
                     end if;
                  end loop;
                  Ada.Text_IO.Put ("]");
               end if;
               Ada.Text_IO.Put (", ");
               Ada.Text_IO.Put
                 (Writes.Values.Element (I).Status.Kind'Image & ")");
            end loop;
            Ada.Text_IO.New_Line;
            case Writes.Kind is
            when Entire_Object =>
               null;
            when Record_Components =>
               Ada.Text_IO.Put_Line (Spaces & "Fields  =>");
               for Position in Writes.Component_Status.Iterate loop
                  Ada.Text_IO.Put_Line
                    (Spaces & "   "
                     & Source_Name (Write_Status_Maps.Key (Position))
                     & " =>");
                  Print_Writes
                    (Write_Status_Maps.Element (Position).all, Padding + 6);
               end loop;
            when Array_Components =>
               Ada.Text_IO.Put_Line (Spaces & "Content =>");
               Print_Writes (Writes.Content_Status.all, Padding + 3);
            end case;
         end Print_Writes;

      --  Start of processing for Print_Writes

      begin
         Print_Writes (Writes, 0);
      end Print_Writes;
      pragma Annotate (Xcov, Exempt_Off);

      ---------------
      -- Propagate --
      ---------------

      procedure Propagate
        (Writes    : not null Write_Status_Access;
         Choices   : Choice_Array;
         Status    : Write_Type;
         Skip_Root : Boolean := False)
      is
      begin
         --  Update the root itself if necessary

         if not Skip_Root then
            Writes.Values.Append
              (Constrained_Value'(Choices'Length, Empty, Status, Choices));
         end if;

         --  Propagate the new association to all subtrees

         case Writes.Kind is
            when Entire_Object =>
               null;

            when Record_Components =>
               for Position in Writes.Component_Status.Iterate loop
                  Propagate
                    (Writes.Component_Status (Position),
                     Choices,
                     Record_Access (Status, Write_Status_Maps.Key (Position)));
               end loop;

            when Array_Components =>
               Propagate
                 (Writes.Content_Status,
                  Choices & Empty,
                  Array_Access (Status, Choices'Length + 1));
         end case;
      end Propagate;

      -----------------
      -- Unfold_Tree --
      -----------------

      procedure Unfold_Tree (Writes : in out not null Write_Status_Access) is
         Old_Writes : Write_Status_Access := Writes;
      begin
         --  If Writes has type Entire_Object, unfold it

         if Writes.Kind = Entire_Object then
            if Is_Record_Type (Old_Writes.Ty) then
               Writes := new
                 Write_Status'
                   (Kind             => Record_Components,
                    Ty               => Old_Writes.Ty,
                    Values           => Old_Writes.Values,
                    Component_Status => Write_Status_Maps.Empty_Map);
            else
               pragma Assert (Is_Array_Type (Old_Writes.Ty));
               declare
                  use Constrained_Value_Vectors;
                  Values : Constrained_Value_Vectors.Vector;
                  --  The array has always been updated as a whole until now.
                  --  To initialize the constrained values of its components,
                  --  use the values of Writes with an additional empty choice
                  --  to state that all indexes are written.

               begin
                  for Pref_Value of Old_Writes.Values loop
                     Values.Append
                       (Constrained_Value '
                          (Size     => Pref_Value.Size + 1,
                           Ada_Node => Pref_Value.Ada_Node,
                           Choices  => Pref_Value.Choices & Types.Empty,
                           Status   => Array_Access
                             (Pref_Value.Status, Pref_Value.Size + 1)));
                  end loop;

                  Writes := new Write_Status'
                    (Kind           => Array_Components,
                     Ty             => Old_Writes.Ty,
                     Values         => Old_Writes.Values,
                     Content_Status => new Write_Status'
                       (Kind   => Entire_Object,
                        Ty     => Retysp (Component_Type (Old_Writes.Ty)),
                        Values => Values));
               end;
            end if;
            Free (Old_Writes);
         end if;
      end Unfold_Tree;

   end Association_Trees;

   ----------------------------
   -- Get_Name_For_Aggregate --
   ----------------------------

   function Get_Name_For_Aggregate (Expr : Node_Id) return String is
      Obj : constant Entity_Id := Get_Initialized_Object (Expr);

   begin
      --  If Expr is used to initialize an object, reuse the object name to get
      --  a stable name.

      if Present (Obj) then
         return Get_Module_Name (E_Module (Obj))
           & To_String (WNE_Aggregate_Def_Suffix);
      else
         return New_Temp_Identifier (To_String (WNE_Aggregate_Def_Suffix));
      end if;
   end Get_Name_For_Aggregate;

   ------------------------------------
   -- Transfrom_Deep_Delta_Aggregate --
   ------------------------------------

   function Transform_Deep_Delta_Aggregate
     (Expr   : Node_Id;
      Domain : EW_Domain;
      Params : Transformation_Params)
      return W_Expr_Id
   is

      function Is_Simple_Record_Aggregate
        (Writes : Write_Status)
         return Boolean;
      --  Return True if Writes contains only record accesses

      function Generate_Simple_Record_Aggregate
        (Writes       : Write_Status;
         Ada_Node     : Node_Id;
         Expr         : W_Expr_Id;
         Relaxed_Init : Boolean;
         Domain       : EW_Domain;
         Params       : Transformation_Params)
         return W_Expr_Id
      with Pre => Writes.Kind = Record_Components
        and then Is_Simple_Record_Aggregate (Writes);
      --  Generate a record update from a tree containing only record accesses

      procedure Get_Aggregate_Elements
        (Writes    : Write_Status;
         Value_Map : in out Ada_Node_To_Why_Id.Map);
      --  Extract parts of the aggregate Expr that will be passed as parameters
      --  to the logic function for the aggregate.
      --  Elements of the aggregate and choice indexes are collected in
      --  Value_Map. They are associated to an identifier which will be used to
      --  refer to them in the aggregate's defining axiom.

      procedure Generate_Context_For_Aggregate
        (Writes        : Write_Status;
         Ada_Node      : Node_Id;
         New_Name      : W_Expr_Id;
         Old_Name      : W_Expr_Id;
         Domain        : EW_Domain;
         Params        : Transformation_Params;
         Indices       : W_Identifier_Array := (1 .. 0 => <>);
         Value_Map     : Ada_Node_To_Why_Id.Map;
         Access_Checks : in out W_Statement_Sequence_Id;
         Pred_Checks   : in out W_Statement_Sequence_Id;
         Context       : in out Ref_Context);
      --  Generate the context for a call to the predicate function. After the
      --  call, Context contains (among other things) bindings for elements of
      --  Value_Map. Access_Checks contains checks for accesses inside Old_Name
      --  and Pred_Checks predicate checks over the final value of the
      --  aggregate New_Name. Access_Checks are performed on the parent first
      --  and then on the components, Pred_Checks are done on the components
      --  before.
      --
      --  The aim is to generate:
      --
      --  (* in Context: *)
      --  let val1 = ... in  (* for each value in an association *)
      --  let idx1 = ... in  (* for each index in a selector *)
      --
      --  (* in Access_Checks: *)
      --  ignore { old_name.<comp> }; (* for each subcomponent comp updated in
      --                                 the aggregate *)
      --  assert {in_range old_name idx1 };  (* for each index in selector *)
      --
      --  (* the call itself is not generated by this procedure *)
      --  let new_name = aggregate idx1 ... val1 ... in
      --
      --  (* in Pred_Checks: *)
      --  ignore { predicate_check new_name.<comp> }
      --  (* for each subcomponent comp updated in the aggregate *)
      --
      --  Context also includes declarations for discriminants, as they can
      --  occur in types of subcomponents. If Writes has non-empty choices (its
      --  prefix contains array accesses), then New_Name and Old_Name are only
      --  defined inside Access_Checks and Pred_Checks as the indices in the
      --  array accesses are modeled using an any expression.

      function Transform_Choice
        (Choice    : Node_Id;
         Index     : W_Identifier_Id;
         Value_Map : Ada_Node_To_Why_Id.Map)
         return W_Pred_Id;
      --  Generates Index = Choice using the mappings in Value_Map to get the
      --  Temporary identifier which should be used for Choice.

      function Transform_Choices
        (Choices   : Choice_Array;
         Indices   : W_Identifier_Array;
         Value_Map : Ada_Node_To_Why_Id.Map)
         return W_Pred_Id
      with Pre => Choices'Length = Indices'Length;
      --  Generate Indices (1) = Choices (1) /\ ...

      function Generate_Pred_For_Aggregate
        (Writes    : Write_Status;
         New_Name  : W_Term_Id;
         Old_Name  : W_Term_Id;
         Value_Map : Ada_Node_To_Why_Id.Map)
         return W_Pred_Id;
      --  Generate a predicate giving the value of New_Name from a value
      --  Old_Name using the updates stored in Writes.

      procedure Generate_Logic_Function
        (Writes       : Write_Status;
         Elements     : Node_Vectors.Vector;
         Ada_Node     : Node_Id;
         Relaxed_Init : Boolean;
         Expr_Id      : W_Identifier_Id;
         Value_Map    : Ada_Node_To_Why_Id.Map);
      --  Generate the logic function definition for writes, with a suitable
      --  defining axiom:
      --
      --     function F (<params>) : <type of aggregate>
      --
      --     axiom A:
      --       forall id:<type of aggregate>. forall <params>.
      --         <predicate generated for the aggregate on F (<params>)>

      function Complete_Translation
        (Writes    : Write_Status;
         Elements  : Node_Vectors.Vector;
         Ada_Node  : Node_Id;
         Expr      : W_Expr_Id;
         Func      : W_Identifier_Id;
         Domain    : EW_Domain;
         Params    : Transformation_Params;
         Value_Map : Ada_Node_To_Why_Id.Map)
         return W_Expr_Id;
      --  Given a logic function Func previously defined for the aggregate,
      --  generate the actual call to Func.

      function Generate_Deep_Delta_Aggregate
        (Writes       : Write_Status;
         Elements     : Node_Vectors.Vector;
         Ada_Node     : Node_Id;
         Expr         : W_Expr_Id;
         Relaxed_Init : Boolean;
         Domain       : EW_Domain;
         Params       : Transformation_Params)
         return W_Expr_Id;
      --  Generate the translation of a deep delta aggregate from an
      --  association tree.

      --------------------------
      -- Complete_Translation --
      --------------------------

      function Complete_Translation
        (Writes    : Write_Status;
         Elements  : Node_Vectors.Vector;
         Ada_Node  : Node_Id;
         Expr      : W_Expr_Id;
         Func      : W_Identifier_Id;
         Domain    : EW_Domain;
         Params    : Transformation_Params;
         Value_Map : Ada_Node_To_Why_Id.Map)
         return W_Expr_Id
      is
         New_Name   : constant W_Identifier_Id :=
           New_Temp_Identifier
             (Typ       => Get_Typ (Func),
              Base_Name => "aggr");
         Old_Name   : constant W_Expr_Id := New_Temp_For_Expr (Expr);

         --  Arrays of arguments

         Num_Params : constant Natural := Natural (Value_Map.Length) + 1;
         Call_Args  : W_Expr_Array (1 .. Num_Params);
         Top        : Natural := 0;

         --  Parts of the completion that need to be put together

         Access_Checks : W_Statement_Sequence_Id := Void_Sequence;
         Pred_Checks   : W_Statement_Sequence_Id := Void_Sequence;
         Context       : Ref_Context;
         Call          : W_Expr_Id;
      begin

         --  Compute the arguments for the call

         Top := Top + 1;
         Call_Args (Top) := Old_Name;

         --  Use a vector to get values and indexes in a meaningfull order

         for Element of Elements loop
            declare
               Element_Id : constant W_Identifier_Id :=
                 Value_Map.Element (Element);
            begin
               Top := Top + 1;
               Call_Args (Top) := +Element_Id;
            end;
         end loop;

         pragma Assert (Top = Num_Params);

         --  Compute the call

         Call := New_Call
           (Name   => Func,
            Domain => Domain,
            Args   => Call_Args,
            Typ    => Get_Typ (Func));

         --  Compute the context for the call

         Generate_Context_For_Aggregate
           (Writes        => Writes,
            Ada_Node      => Ada_Node,
            New_Name      => +New_Name,
            Old_Name      => Old_Name,
            Domain        => Domain,
            Params        => Params,
            Value_Map     => Value_Map,
            Access_Checks => Access_Checks,
            Pred_Checks   => Pred_Checks,
            Context       => Context);

         --  In the program domain, add the checks to Call

         if Domain = EW_Prog then
            Call := +Sequence
              (+Access_Checks,
               New_Binding
                 (Name    => New_Name,
                  Def     => +Call,
                  Context => Sequence (+Pred_Checks, +New_Name),
                  Typ     => Get_Typ (New_Name)));
         end if;

         --  Introduce the context

         for Ref of Context loop
            pragma Assert (not Ref.Mutable);
            Call := New_Binding
              (Name    => Ref.Name,
               Def     => Ref.Value,
               Domain  => Domain,
               Context => Call);
         end loop;

         --  Insert a reference for the base expression if necessary

         Call := Binding_For_Temp
           (Domain  => Domain,
            Tmp     => Old_Name,
            Context => Call);

         return Call;

      end Complete_Translation;

      ------------------------------------
      -- Generate_Context_For_Aggregate --
      ------------------------------------

      procedure Generate_Context_For_Aggregate
        (Writes        : Write_Status;
         Ada_Node      : Node_Id;
         New_Name      : W_Expr_Id;
         Old_Name      : W_Expr_Id;
         Domain        : EW_Domain;
         Params        : Transformation_Params;
         Indices       : W_Identifier_Array := (1 .. 0 => <>);
         Value_Map     : Ada_Node_To_Why_Id.Map;
         Access_Checks : in out W_Statement_Sequence_Id;
         Pred_Checks   : in out W_Statement_Sequence_Id;
         Context       : in out Ref_Context)
      is
         Top_Level : constant Boolean := Indices'Length = 0;
         --  The accesses that occur at top-level (ie. not under an array
         --  indexed component) are handled specifically.

      begin
         --  Go over the constrained values of Writes and introduce a mapping
         --  in the context for those which are entirely written.

         for C_Value of Writes.Values loop
            if C_Value.Status.Kind = Entire
              and then C_Value.Status.Path.Kind = Root
            then
               declare
                  W_Id : constant W_Identifier_Id := Value_Map.Element
                    (C_Value.Status.Path.Expr);
               begin
                  Context.Append
                    (Ref_Type'
                       (Mutable => False,
                        Name    => W_Id,
                        Value   => Transform_Expr
                          (Expr          => C_Value.Status.Path.Expr,
                           Expected_Type => Get_Typ (W_Id),
                           Domain        => Domain,
                           Params        => Params)));
               end;
            end if;
         end loop;

         --  Go over the potential component writes to generate the context for
         --  them.

         case Writes.Kind is

            --  The object is entirely written, there is nothing more to do

            when Entire_Object =>
               null;

            when Record_Components =>

               --  As discriminants may occur as bounds in types of
               --  discriminant dependent components, store them in the symbol
               --  table.

               Ada_Ent_To_Why.Push_Scope (Symbol_Table);

               if Has_Discriminants (Writes.Ty) then

                  --  If there are no array accesses in the path, get the
                  --  discriminants from the old value.

                  if Top_Level then
                     declare
                        D : Entity_Id := First_Discriminant (Writes.Ty);
                     begin
                        while Present (D) loop
                           declare
                              W_Id : constant W_Identifier_Id :=
                                New_Temp_Identifier
                                  (Typ       => EW_Abstract (Etype (D)),
                                   Base_Name => "discr");
                           begin
                              Context.Append
                                (Ref_Type'(Mutable => False,
                                           Name    => W_Id,
                                           Value   => New_Ada_Record_Access
                                             (Ada_Node => Empty,
                                              Domain   => Term_Domain (Domain),
                                              Name     => Old_Name,
                                              Field    => D,
                                              Ty       => Writes.Ty)));

                              Insert_Tmp_Item_For_Entity (D, W_Id);
                           end;

                           Next_Discriminant (D);
                        end loop;
                     end;

                  --  Otherwise, get the discriminants from the type
                  --  constraints.

                  elsif Is_Constrained (Writes.Ty) then
                     declare
                        D    : Entity_Id := First_Discriminant (Writes.Ty);
                        Elmt : Elmt_Id :=
                          First_Elmt (Discriminant_Constraint ((Writes.Ty)));

                     begin
                        while Present (D) loop
                           declare
                              W_Id : constant W_Identifier_Id :=
                                New_Temp_Identifier
                                  (Typ       => EW_Abstract (Etype (D)),
                                   Base_Name => "discr");
                           begin
                              Context.Append
                                (Ref_Type'
                                   (Mutable => False,
                                    Name    => W_Id,
                                    Value   =>
                                      Transform_Expr
                                        (Domain        => Domain,
                                         Params        => Params,
                                         Expr          => Node (Elmt),
                                         Expected_Type => Get_Typ (W_Id))));

                              Insert_Tmp_Item_For_Entity (D, W_Id);
                           end;

                           Next_Elmt (Elmt);
                           Next_Discriminant (D);
                        end loop;
                     end;

                  --  If the discriminants are mutable, associations should not
                  --  not depend on their values in paths containing array
                  --  accesses.

                  else
                     pragma Assert (Has_Defaulted_Discriminants (Writes.Ty));
                  end if;
               end if;

               --  Go over the record fields to accumulate their context

               for Position in Writes.Component_Status.Iterate loop
                  declare
                     use Write_Status_Maps;
                     Comp     : constant Entity_Id := Key (Position);
                     C_Writes : constant Write_Status_Access :=
                       Element (Position);
                     C_Acc    : W_Expr_Id;
                     C_Node   : Node_Id := Types.Empty;

                  begin
                     --  To locate the checks, search for the first association
                     --  with a non-empty Ada node.

                     for C_Value of C_Writes.Values loop
                        if Present (C_Value.Ada_Node) then
                           C_Node := C_Value.Ada_Node;
                           exit;
                        end if;
                     end loop;

                     C_Acc := New_Ada_Record_Access
                       (Ada_Node => C_Node,
                        Domain   => Domain,
                        Name     => Old_Name,
                        Field    => Comp,
                        Ty       => Writes.Ty);

                     --  If the record has discriminants and we are in the
                     --  program domain, C_Acc might contain checks. If we are
                     --  at top-level, introduce a temporary for it.

                     if Has_Discriminants (Writes.Ty) and then Domain = EW_Prog
                     then
                        if Top_Level then
                           declare
                              W_Id : constant W_Identifier_Id :=
                                New_Temp_Identifier
                                  (Typ       => Get_Type (C_Acc),
                                   Base_Name => "rec_acc");
                           begin
                              Context.Append
                                (Ref_Type'
                                   (Mutable => False,
                                    Name    => W_Id,
                                    Value   => C_Acc));
                              C_Acc := +W_Id;
                           end;

                        --  Otherwise, New_Name and Old_Name are only defined
                        --  inside checks. Put the checked access in an ignore
                        --  block and use an unchecked access instead.

                        else
                           Append (Access_Checks, New_Ignore (Prog => +C_Acc));

                           C_Acc := New_Ada_Record_Access
                             (Ada_Node => C_Node,
                              Domain   => EW_Pterm,
                              Name     => Old_Name,
                              Field    => Comp,
                              Ty       => Writes.Ty);
                        end if;
                     end if;

                     Generate_Context_For_Aggregate
                       (Writes        => C_Writes.all,
                        Ada_Node      => C_Node,
                        New_Name      => New_Ada_Record_Access
                          (Ada_Node => C_Node,
                           Domain   => Term_Domain (Domain),
                           Name     => New_Name,
                           Field    => Comp,
                           Ty       => Writes.Ty),
                        Old_Name      => C_Acc,
                        Domain        => Domain,
                        Params        => Params,
                        Indices       => Indices,
                        Value_Map     => Value_Map,
                        Access_Checks => Access_Checks,
                        Pred_Checks   => Pred_Checks,
                        Context       => Context);
                  end;
               end loop;

               Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

            when Array_Components =>

               --  Introduce bindings and checks for the index values

               for C_Value of Writes.Content_Status.Values loop
                  if Present (C_Value.Choices (C_Value.Size)) then
                     declare
                        W_Id : constant W_Identifier_Id := Value_Map.Element
                          (C_Value.Choices (C_Value.Size));
                     begin
                        Context.Append
                          (Ref_Type'
                             (Mutable => False,
                              Name    => W_Id,
                              Value   => Transform_Expr
                                (Expr          =>
                                     C_Value.Choices (C_Value.Size),
                                 Domain        => Domain,
                                 Params        => Params,
                                 Expected_Type => Get_Typ (W_Id))));

                        if Domain = EW_Prog then
                           Append
                             (Access_Checks,
                              New_Ignore
                                (Prog => Do_Index_Check
                                     (Ada_Node =>
                                          C_Value.Choices (C_Value.Size),
                                      Arr_Expr => +Old_Name,
                                      W_Expr   => +W_Id,
                                      Dim      => 1)));
                        end if;
                     end;
                  end if;
               end loop;

               --  To create a name for the component accesses of Old_Name and
               --  New_Name, we need an index value. These names will only be
               --  used inside access and predicate checks. Therefore, it is
               --  enough to bind the index identifier in both sequences of
               --  checks (as opposed to binding it globally).

               declare
                  Idx_Id       : constant W_Identifier_Id :=
                    New_Temp_Identifier
                      (Typ       => Nth_Index_Rep_Type_No_Bool (Writes.Ty, 1),
                       Base_Name => "index");
                  Content_Node : Node_Id := Empty;
                  Content_Acc  : W_Statement_Sequence_Id  := Void_Sequence;
                  Content_Pred : W_Statement_Sequence_Id  := Void_Sequence;

               begin
                  --  To locate the checks, search for the first association
                  --  with a non-empty Ada node in Content_Status.

                  for C_Value of Writes.Content_Status.Values loop
                     if Present (C_Value.Ada_Node) then
                        Content_Node := C_Value.Ada_Node;
                        exit;
                     end if;
                  end loop;

                  Generate_Context_For_Aggregate
                    (Writes        => Writes.Content_Status.all,
                     Ada_Node      => Content_Node,
                     New_Name      => New_Array_Access
                       (Ar     => +New_Name,
                        Index  => (1 => +Idx_Id),
                        Domain => Term_Domain (Domain)),
                     Old_Name      => New_Array_Access
                       (Ar     => +Old_Name,
                        Index  => (1 => +Idx_Id),
                        Domain => Term_Domain (Domain)),
                     Domain        => Domain,
                     Params        => Params,
                     Indices       => Indices & Idx_Id,
                     Value_Map     => Value_Map,
                     Access_Checks => Content_Acc,
                     Pred_Checks   => Content_Pred,
                     Context       => Context);

                  --  In the Prog domain, append Content_Acc and Content_Pred
                  --  to the parameter check sequences. The indice is bound to
                  --  all possible values corresponding to an updated index.

                  if Domain = EW_Prog then
                     declare
                        Result      : constant W_Identifier_Id :=
                          New_Result_Ident (Get_Typ (Idx_Id));
                        Constraints : W_Pred_Array
                          (1 ..  Writes.Content_Status.Values.Last_Index);
                        Top         : Natural := 0;

                     begin
                        --  Go over the constrained values of Content_Status to
                        --  collect the constraints of paths which are not
                        --  preserved in Constraints. This is used to only
                        --  perform the checks on indices which are actually
                        --  written in the aggregate.

                        for C_Value of Writes.Content_Status.Values loop
                           if C_Value.Status.Kind /= Preserved then
                              Top := Top + 1;
                              Constraints (Top) := Transform_Choices
                                (Choices   => C_Value.Choices,
                                 Indices   => Indices & Result,
                                 Value_Map => Value_Map);
                           end if;
                        end loop;

                        --  Generate an any expr to model an index at which the
                        --  array is updated.

                        declare
                           Old_Def : constant W_Prog_Id := New_Any_Expr
                             (Post        => New_And_Pred
                                (Left  => +New_Array_Range_Expr
                                     (+Result, +Old_Name, EW_Pred, 1),
                                 Right => New_Or_Pred
                                   (Conjuncts => Constraints (1 .. Top))),
                              Return_Type => Get_Typ (Idx_Id),
                              Labels      => Symbol_Sets.Empty_Set);
                           New_Def : constant W_Prog_Id := New_Any_Expr
                             (Post        => New_And_Pred
                                (Left  => +New_Array_Range_Expr
                                     (+Result, +Old_Name, EW_Pred, 1),
                                 Right => New_Or_Pred
                                   (Conjuncts => Constraints (1 .. Top))),
                              Return_Type => Get_Typ (Idx_Id),
                              Labels      => Symbol_Sets.Empty_Set);
                        begin
                           Append
                             (Access_Checks,
                              New_Binding
                                (Name    => Idx_Id,
                                 Def     => Old_Def,
                                 Context => +Content_Acc));
                           Prepend
                             (New_Binding
                                (Name    => Idx_Id,
                                 Def     => New_Def,
                                 Context => +Content_Pred),
                              Pred_Checks);
                        end;
                     end;
                  end if;
               end;
         end case;

         --  If the target type has a direct or inherited predicate, generate a
         --  corresponding check. Do not generate predicate checks for entire
         --  updates, as in this case the predicate has been checked on the
         --  provided value.

         if Writes.Kind /= Entire_Object
           and then Domain = EW_Prog
           and then Has_Predicates (Writes.Ty)
         then
            Prepend
              (New_Predicate_Check (Ada_Node => Ada_Node,
                                    Ty       => Writes.Ty,
                                    W_Expr   => New_Name),
               Pred_Checks);
         end if;

      end Generate_Context_For_Aggregate;

      -----------------------------------
      -- Generate_Deep_Delta_Aggregate --
      -----------------------------------

      function Generate_Deep_Delta_Aggregate
        (Writes       : Write_Status;
         Elements     : Node_Vectors.Vector;
         Ada_Node     : Node_Id;
         Expr         : W_Expr_Id;
         Relaxed_Init : Boolean;
         Domain       : EW_Domain;
         Params       : Transformation_Params)
         return W_Expr_Id
      is
      begin
         if Is_Simple_Record_Aggregate (Writes) then
            return Generate_Simple_Record_Aggregate
              (Writes       => Writes,
               Ada_Node     => Ada_Node,
               Expr         => Insert_Simple_Conversion
                 (Expr   => Expr,
                  Domain => Domain,
                  To     => EW_Abstract (Writes.Ty, Relaxed_Init)),
               Relaxed_Init => Relaxed_Init,
               Domain       => Domain,
               Params       => Params);
         end if;

         declare
            use all type Ada.Containers.Count_Type;
            Index_Map : Ada_Node_To_Why_Id.Map;
            Value_Map : Ada_Node_To_Why_Id.Map;
         begin
            Get_Aggregate_Elements
              (Writes    => Writes,
               Value_Map => Value_Map);

            pragma Assert
              (Elements.Length = Index_Map.Length + Value_Map.Length);

            --  If not done already, generate the logic function

            declare
               M : W_Module_Id := E_Module (Ada_Node);
            begin
               if M = Why_Empty then
                  Generate_Logic_Function
                    (Ada_Node     => Ada_Node,
                     Writes       => Writes,
                     Elements     => Elements,
                     Relaxed_Init => Relaxed_Init,
                     Expr_Id      => New_Temp_Identifier
                       (Typ       => Get_Type (Expr),
                        Base_Name => "base"),
                     Value_Map    => Value_Map);
                  M := E_Module (Ada_Node);
               end if;

               return Complete_Translation
                 (Writes    => Writes,
                  Elements  => Elements,
                  Ada_Node  => Ada_Node,
                  Expr      => Expr,
                  Func      => New_Identifier
                    (Ada_Node => Ada_Node,
                     Domain   => Domain,
                     Module   => M,
                     Symb     => NID (Lower_Case_First (Img (Get_Name (M)))),
                     Typ      => EW_Abstract (Writes.Ty, Relaxed_Init)),
                  Domain    => Domain,
                  Params    => Params,
                  Value_Map => Value_Map);
            end;
         end;
      end Generate_Deep_Delta_Aggregate;

      -----------------------------
      -- Generate_Logic_Function --
      -----------------------------

      procedure Generate_Logic_Function
        (Writes       : Write_Status;
         Elements     : Node_Vectors.Vector;
         Ada_Node     : Node_Id;
         Relaxed_Init : Boolean;
         Expr_Id      : W_Identifier_Id;
         Value_Map    : Ada_Node_To_Why_Id.Map)
      is
         Name          : constant String :=
           Lower_Case_First (Get_Name_For_Aggregate (Ada_Node));
         Module        : constant W_Module_Id :=
           New_Module
             (Ada_Node => Ada_Node,
              File     => No_Symbol,
              Name     => Name);
         Func          : constant W_Identifier_Id :=
           New_Identifier
             (Ada_Node => Ada_Node,
              Domain   => EW_Pterm,
              Module   => Module,
              Symb     => NID (Name));

         --  Arrays of binders and arguments

         Num_Params    : constant Natural := Natural (Value_Map.Length) + 1;
         Call_Params   : Binder_Array (1 .. Num_Params);
         Call_Args     : W_Expr_Array (1 .. Num_Params);
         Top           : Natural := 0;

         --  Variables for the call and proposition for the axiom

         Aggr          : W_Term_Id;
         Def_Pred      : W_Pred_Id;
         Axiom_Body    : W_Pred_Id;

         Aggr_Temp     : constant W_Identifier_Id :=
           New_Temp_Identifier
             (Typ       => EW_Abstract (Writes.Ty, Relaxed_Init),
              Base_Name => "aggr");

         Th            : Theory_UC;

      --  Start of processing for Generate_Logic_Function

      begin
         --  Insert new modules for the logic function in the module map

         Insert_Extra_Module (Ada_Node, Module);
         Insert_Extra_Module
           (Ada_Node,
            New_Module (File => No_Symbol,
                        Name => Name & To_String (WNE_Axiom_Suffix)),
            Is_Axiom => True);

         --  Compute the parameters/arguments for the axiom/call

         Top := Top + 1;
         Call_Params (Top) := Binder_Type'
           (Ada_Node => Empty,
            B_Name   => Expr_Id,
            B_Ent    => Null_Entity_Name,
            Mutable  => False,
            Labels   => Symbol_Sets.Empty_Set);

         --  Use Elements to get the values and indexes in a meaningful order

         for Element of Elements loop
            declare
               Element_Id : constant W_Identifier_Id :=
                 Value_Map.Element (Element);
            begin
               Top := Top + 1;
               Call_Params (Top) := Binder_Type'
                 (Ada_Node => Standard.Types.Empty,
                  B_Name   => Element_Id,
                  B_Ent    => Null_Entity_Name,
                  Mutable  => False,
                  Labels   => Symbol_Sets.Empty_Set);
            end;
         end loop;

         pragma Assert (Top = Num_Params);

         Call_Args := Get_Args_From_Binders
           (Call_Params, Ref_Allowed => False);

         --  Compute the proposition for the axiom

         Axiom_Body := Generate_Pred_For_Aggregate
           (Writes    => Writes,
            New_Name  => +Aggr_Temp,
            Old_Name  => +Expr_Id,
            Value_Map => Value_Map);

         Aggr :=
           New_Call (Ada_Node => Ada_Node,
                     Name     => Func,
                     Args     => Call_Args,
                     Typ      => Get_Typ (Aggr_Temp));

         Def_Pred :=
           New_Typed_Binding
             (Name    => Aggr_Temp,
              Def     => Aggr,
              Context => Axiom_Body);

         --  Generate the logic function declaration

         Th :=
           Open_Theory
             (WF_Context, E_Module (Ada_Node),
              Comment =>
                "Module for declaring an abstract function for the deep delta "
              & "aggregate at "
              & (if Sloc (Ada_Node) > 0 then
                   Build_Location_String (Sloc (Ada_Node))
                else "<no location>")
              & ", created in " & GNAT.Source_Info.Enclosing_Entity);

         Emit (Th,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        => To_Local (Func),
                  Labels      => Symbol_Sets.Empty_Set,
                  Location    => No_Location,
                  Binders     => Call_Params,
                  Return_Type => Get_Typ (Aggr_Temp)));

         Close_Theory (Th,
                       Kind           => Definition_Theory,
                       Defined_Entity => Ada_Node);

         --  Generate the axiom in a completion module

         Th :=
           Open_Theory
             (WF_Context, E_Module (Ada_Node, Axiom),
              Comment =>
                "Module for defining the value of the deep delta aggregate at "
              & (if Sloc (Ada_Node) > 0 then
                   Build_Location_String (Sloc (Ada_Node))
                else "<no location>")
              & ", created in " & GNAT.Source_Info.Enclosing_Entity);

         Emit (Th,
               New_Guarded_Axiom
                 (Name     => NID (Def_Axiom),
                  Binders  => Call_Params,
                  Def      => Def_Pred,
                  Triggers => New_Triggers
                    (Triggers =>
                         (1 => New_Trigger
                              (Terms =>
                                 (1 => New_Call
                                    (Ada_Node => Ada_Node,
                                     Domain   => EW_Term,
                                     Name     => Func,
                                     Args     => Call_Args,
                                     Typ      => Get_Typ (Aggr_Temp)))))),
                  Dep      =>
                    New_Axiom_Dep (Name => Func,
                                   Kind => EW_Axdep_Func)));

         Close_Theory (Th,
                       Kind           => Axiom_Theory,
                       Defined_Entity => Ada_Node);
      end Generate_Logic_Function;

      ---------------------------------
      -- Generate_Pred_For_Aggregate --
      ---------------------------------

      function Generate_Pred_For_Aggregate
        (Writes    : Write_Status;
         New_Name  : W_Term_Id;
         Old_Name  : W_Term_Id;
         Value_Map : Ada_Node_To_Why_Id.Map)
         return W_Pred_Id
      is

         function Other_Choices
           (Values  : Constrained_Value_Vectors.Vector;
            Indices : W_Identifier_Array)
            return W_Pred_Id
         with Pre => (for all Value of Values => Value.Size = Indices'Length);
         --  Return a predicate expressing that indices in Indices correspond
         --  to preserved choices of Values. Concrete values for indices inside
         --  Values should be stored in Index_Map.

         function Transform_Path
           (Path    : Path_Type;
            Indices : W_Identifier_Array)
            return W_Term_Id;
         --  Transform a path into a Why expression. The root of Path should be
         --  stored in Value_Map.

         function New_Conditional
           (Conditions : W_Pred_Array;
            Predicates : W_Pred_Array)
            return W_Pred_Id
         with Pre => Predicates'Length = Conditions'Length + 1;
         --  Construct a conditional from an array of conditions and an array
         --  of consequences.

         function Has_Additional_Writes
           (Prefix_Values : Constrained_Value_Vectors.Vector;
            Comp_Values   : Constrained_Value_Vectors.Vector)
            return Boolean
         is
           (for some I in 1 .. Prefix_Values.Last_Index =>
               Prefix_Values.Element (I).Status.Kind = Partial
            and then Comp_Values.Element (I).Status.Kind = Entire);
         --  Return True if there is a choice for which the current component
         --  is entirely written but not its prefix.

         function Is_Written_For_All_Choices
           (Prefix_Values : Constrained_Value_Vectors.Vector;
            Comp_Values   : Constrained_Value_Vectors.Vector)
            return Boolean
         is
           (for all I in 1 .. Prefix_Values.Last_Index =>
              (if Prefix_Values.Element (I).Status.Kind = Partial
               then Comp_Values.Element (I).Status.Kind /= Preserved));
         --  Return True if, for all choices which are not preserved in the
         --  prefix, the component is written (at least partially).

         procedure Collect_Preserved_Fields
           (Writes : Write_Status;
            Prefix : W_Term_Id;
            Values : W_Term_Array;
            Eqs    : in out W_Pred_Array);
         --  Collect in Eqs (I) a predicate stating that, for all record
         --  subcomponents which are preserved in Writes, the subcomponent of
         --  Prefix is equal to the subcomponent of Values (I). The
         --  subcomponents which are preserved are those which do not have
         --  their own branch in the tree. If the root of a subtree is written
         --  directly (see Has_Additional_Writes) then its components are all
         --  written.

         function Generate_Values_For_Record_Updates
           (Writes      : Write_Status;
            New_Name    : W_Term_Id;
            Old_Name    : W_Term_Id;
            Root_Values : Constrained_Value_Vectors.Vector;
            Indices     : W_Identifier_Array)
            return W_Pred_Id
         with Pre => Writes.Kind = Record_Components;
         --  Generate a predicate giving the values of all the record
         --  subcomponents which are mentioned in Writes. The ones which are
         --  not mentionned should be handled separately, see
         --  Collect_Preserved_Fields.

         function Generate_Aggregate_Value_Internal
           (Writes      : Write_Status;
            New_Name    : W_Term_Id;
            Old_Name    : W_Term_Id;
            Root_Values : Constrained_Value_Vectors.Vector;
            Indices     : W_Identifier_Array)
            return W_Pred_Id;
         --  Generate a predicate giving the value of New_Name from a value
         --  Old_Name using the updates stored in Writes. Do not consider
         --  indices which are preserved in Root_Values.

         ------------------------------
         -- Collect_Preserved_Fields --
         ------------------------------

         procedure Collect_Preserved_Fields
           (Writes : Write_Status;
            Prefix : W_Term_Id;
            Values : W_Term_Array;
            Eqs    : in out W_Pred_Array)
         is
         begin
            case Writes.Kind is
               when Entire_Object | Array_Components =>
                  null;

               when Record_Components =>

                  --  Discriminants are preserved

                  if Has_Discriminants (Writes.Ty) then
                     declare
                        Discr : Entity_Id := First_Discriminant (Writes.Ty);
                     begin
                        while Present (Discr) loop
                           for I in Values'Range loop
                              Eqs (I) := New_And_Pred
                                (Left  => Eqs (I),
                                 Right => New_Comparison
                                   (Symbol => Why_Eq,
                                    Left   => New_Ada_Record_Access
                                      (Name  => Prefix,
                                       Field => Discr,
                                       Ty    => Writes.Ty),
                                    Right  => New_Ada_Record_Access
                                      (Name  => Values (I),
                                       Field => Discr,
                                       Ty    => Writes.Ty)));
                           end loop;
                           Next_Discriminant (Discr);
                        end loop;
                     end;
                  end if;

                  --  Components which are not mentioned in the tree are
                  --  preserved.

                  for Comp of Get_Component_Set (Writes.Ty) loop
                     declare
                        Position : constant Write_Status_Maps.Cursor :=
                          Writes.Component_Status.Find (Comp);
                        use Write_Status_Maps;
                     begin
                        if Position = No_Element then
                           for I in Values'Range loop
                              declare
                                 Pref_Comp : constant W_Term_Id :=
                                   New_Ada_Record_Access
                                     (Name  => Prefix,
                                      Field => Comp,
                                      Ty    => Writes.Ty);

                              begin
                                 --  A conversion might be needed if the prefix
                                 --  has relaxed initialization and not the
                                 --  value.

                                 Eqs (I) := New_And_Pred
                                   (Left  => Eqs (I),
                                    Right => New_Comparison
                                      (Symbol => Why_Eq,
                                       Left   => Pref_Comp,
                                       Right  => Insert_Simple_Conversion
                                         (Expr           =>
                                              New_Ada_Record_Access
                                               (Name  => Values (I),
                                                Field => Comp,
                                                Ty    => Writes.Ty),
                                          To             =>
                                            Get_Type (+Pref_Comp),
                                          Force_No_Slide => True)));
                              end;
                           end loop;

                        --  Also include preserved subcomponents of Comp if
                        --  Comp is not directly written.

                        elsif not Has_Additional_Writes
                          (Writes.Values, Element (Position).Values)
                        then
                           Collect_Preserved_Fields
                             (Writes => Element (Position).all,
                              Prefix => New_Ada_Record_Access
                                (Name  => Prefix,
                                 Field => Comp,
                                 Ty    => Writes.Ty),
                              Values =>
                                (for Val of Values => New_Ada_Record_Access
                                     (Name  => Val,
                                      Field => Comp,
                                      Ty    => Writes.Ty)),
                              Eqs    => Eqs);
                        end if;
                     end;
                  end loop;
            end case;
         end Collect_Preserved_Fields;

         ---------------------------------------
         -- Generate_Aggregate_Value_Internal --
         ---------------------------------------

         function Generate_Aggregate_Value_Internal
           (Writes      : Write_Status;
            New_Name    : W_Term_Id;
            Old_Name    : W_Term_Id;
            Root_Values : Constrained_Value_Vectors.Vector;
            Indices     : W_Identifier_Array)
         return W_Pred_Id
         is
            Result        : W_Pred_Id;
            Needs_Default : constant Boolean :=
              Writes.Values.First_Element.Size > 0
              and then
                not Is_Written_For_All_Choices (Root_Values, Writes.Values);
            --  If there is no arrays access in the prefix (choices have size
            --  0) or if the object is written on all choices that can reach
            --  the current value from the root of the subtree, then it is not
            --  necessary to add a default case new_name = old_name.

         begin
            case Writes.Kind is
               when Entire_Object =>

                  --  For a sequence of constrained values:
                  --
                  --    (choices_1, status_1) .. (choices_n, status_n)
                  --
                  --  generate:
                  --
                  --    if choices_n then new_name = <status_n.value>
                  --    elsif ...
                  --    else new_name = old_name
                  --
                  --  Choices whose status is "preserved" are ignored, status
                  --  of entire objects cannot be partial. The last condition
                  --  and else branch are omitted if the default association is
                  --  unreachable, see Needs_Default.

                  declare
                     Num_Cond   : constant Positive :=
                       Writes.Values.Last_Index;
                     Conditions : W_Pred_Array (1 .. Num_Cond);
                     Eqs        : W_Pred_Array (1 .. Num_Cond + 1);
                     Top        : Natural := 0;

                  begin
                     for I in reverse 1 .. Num_Cond loop
                        declare
                           C_Value : constant Constrained_Value :=
                             Writes.Values.Element (I);
                           Term    : W_Term_Id;
                        begin
                           case C_Value.Status.Kind is
                              when Partial   =>
                                 raise Program_Error;

                              when Preserved =>
                                 null;

                              when Entire    =>
                                 Top := Top + 1;
                                 Conditions (Top) := Transform_Choices
                                   (Choices   => C_Value.Choices,
                                    Indices   => Indices,
                                    Value_Map => Value_Map);

                                 --  ??? Should we special case the case of
                                 --  simple integer values? Work on the split
                                 --  form and add the dynamic property as a
                                 --  guard + assume the init field like is done
                                 --  for array aggregates?

                                 Term := Transform_Path
                                   (Path    => C_Value.Status.Path,
                                    Indices => Indices);

                                 --  A conversion might be needed if the result
                                 --  has relaxed initialization and not the
                                 --  value.

                                 Term := Insert_Simple_Conversion
                                   (Expr           => Term,
                                    To             => Get_Type (+New_Name),
                                    Force_No_Slide => True);

                                 --  Update the tag if present

                                 if Is_Record_Type_In_Why (Writes.Ty) then
                                    Term := New_Tag_Update
                                      (Name => Term, Ty => Writes.Ty);
                                 end if;

                                 Eqs (Top) := New_Comparison
                                   (Symbol => Why_Eq,
                                    Left   => New_Name,
                                    Right  => Term);
                           end case;
                        end;
                     end loop;

                     --  Add the default case if necessary.
                     --  A conversion might be needed if the result has relaxed
                     --  initialization and not the base expression.

                     if Needs_Default then
                        Top := Top + 1;
                        Eqs (Top) := New_Comparison
                          (Symbol => Why_Eq,
                           Left   => New_Name,
                           Right  => Insert_Simple_Conversion
                             (Expr           => Old_Name,
                              To             => Get_Type (+New_Name),
                              Force_No_Slide => True));
                     end if;

                     Result := New_Conditional
                       (Conditions => Conditions (1 .. Top - 1),
                        Predicates => Eqs (1 .. Top));
                  end;

               when Record_Components =>

                  --  For a sequence of constrained values:
                  --
                  --    (choices_1, status_1) .. (choices_n, status_n)
                  --
                  --  generate:
                  --
                  --   (if choices_n
                  --    then new_name.pres_1 = <status_n.value>.pres_1
                  --      /\ new_name.pres_2 = <status_n.value>.pres_2
                  --      /\ ...
                  --    elsif ...
                  --    else new_name.pres_1 = old_name.pres_1
                  --      /\ new_name.pres_2 = old_name.pres_2
                  --      /\ ...)
                  --    /\ <predicate generated for writ_1>
                  --    /\ <predicate generated for writ_2>
                  --    /\ ...
                  --
                  --  Where the pres_i components are those which are not
                  --  mentioned in the tree and the writ_i components those
                  --  which are written, partially or entirely. No component
                  --  can be entirely preserved or it would not be mentionned
                  --  in the tree. Choices whose status is "preserved" are
                  --  ignored.

                  --  First generate a single conditional for the values of the
                  --  preserved subcomponents.

                  declare
                     Num_Cond   : constant Positive :=
                       Writes.Values.Last_Index;
                     Conditions : W_Pred_Array (1 .. Num_Cond);
                     Terms      : W_Term_Array (1 .. Num_Cond);
                     Eqs        : W_Pred_Array (1 .. Num_Cond + 1) :=
                       (others => True_Pred);
                     Top        : Natural := 0;

                  begin
                     --  Fill the Terms and Conditions array with the choices
                     --  and written values for the different possible index
                     --  values. If there are no array indexes, there is at
                     --  most one value.

                     for I in reverse 1 .. Num_Cond loop
                        declare
                           C_Value : constant Constrained_Value :=
                             Writes.Values.Element (I);
                        begin
                           case C_Value.Status.Kind is
                           when Partial | Preserved =>
                              null;
                           when Entire =>
                              Top := Top + 1;
                              Conditions (Top) := Transform_Choices
                                (Choices   => C_Value.Choices,
                                 Indices   => Indices,
                                 Value_Map => Value_Map);
                              Terms (Top) := Transform_Path
                                (Path    => C_Value.Status.Path,
                                 Indices => Indices);
                           end case;
                        end;
                     end loop;

                     pragma Assert
                       (if Writes.Values.First_Element.Size = 0 then Top <= 1);

                     --  Generate predicates for the preservation of each
                     --  preserved field if any.

                     Collect_Preserved_Fields
                       (Writes => Writes,
                        Prefix => New_Name,
                        Values => Terms (1 .. Top) & Old_Name,
                        Eqs    => Eqs (1 .. Top + 1));

                     --  Create a single condition giving their values

                     if Is_True_Boolean (+Eqs (1)) then
                        Result := True_Pred;
                     else
                        Result := New_Conditional
                          (Conditions => Conditions (1 .. Top),
                           Predicates => Eqs (1 .. Top + 1));
                     end if;
                  end;

                  --  Generate the predicate for the components which are
                  --  written.

                  Result := New_And_Pred
                    (Left  => Result,
                     Right => Generate_Values_For_Record_Updates
                       (Writes      => Writes,
                        New_Name    => New_Name,
                        Old_Name    => Old_Name,
                        Root_Values => Root_Values,
                        Indices     => Indices));

               when Array_Components =>

                  --  For a sequence of constrained values:
                  --
                  --    (choices_1 & choice_1, status_1) ..
                  --               (choices_n & choice_n, status_n)
                  --
                  --  generate:
                  --
                  --    if not choices_1 /\ .. /\ not choices_n
                  --    then new_name = old_name
                  --    else
                  --      new_name.first = old_name.first
                  --      /\ new_name.last = old_name.last
                  --      /\ (for all J =>
                  --           old_name.first <= J <= old_name.last ->
                  --           (if not (choices_1 /\ choice_1) /\ ..
                  --               /\ not (choices_n /\ choice_n)
                  --            then new_name (J) = old_name (J)
                  --            else <predicate generated for array content>))
                  --
                  --  Choices whose status is "preserved" are ignored. The
                  --  top-level conditional is not emitted if the default
                  --  association is unreachable.
                  --
                  --  Conversions might be needed if the result has relaxed
                  --  initialization and not the base expression.

                  --  Generate the nested conditional

                  declare
                     Index    : constant W_Identifier_Id :=
                       New_Temp_Identifier
                         (Typ       =>
                            Nth_Index_Rep_Type_No_Bool (Writes.Ty, 1),
                          Base_Name => "idx");
                     New_Comp : constant W_Term_Id := New_Array_Access
                       (Ar => New_Name, Index => (1 => +Index));
                     Old_Comp : constant W_Term_Id := New_Array_Access
                       (Ar => Old_Name, Index => (1 => +Index));

                  begin
                     Result := New_Conditional
                       (Condition => Other_Choices
                          (Values  => Writes.Content_Status.Values,
                           Indices => Indices & Index),
                        Then_Part => New_Comparison
                          (Symbol => Why_Eq,
                           Left   => New_Comp,
                           Right  => Insert_Simple_Conversion
                             (Expr           => Old_Comp,
                              To             => Get_Type (+New_Comp),
                              Force_No_Slide => True)),
                        Else_Part => Generate_Aggregate_Value_Internal
                          (Writes      => Writes.Content_Status.all,
                           New_Name    => New_Comp,
                           Old_Name    => Old_Comp,
                           Root_Values => Writes.Content_Status.Values,
                           Indices     => Indices & Index));

                     --  Wrap result in a quantification. The indexes are
                     --  constrained to be in the range of the array.

                     Result := New_Universal_Quantif
                       (Variables => (1 => Index),
                        Labels    => Symbol_Sets.Empty_Set,
                        Var_Type  => Get_Typ (Index),
                        Triggers  => New_Triggers
                          (Triggers =>
                               (1 => New_Trigger (Terms => (1 => +New_Comp)),
                                2 => New_Trigger (Terms => (1 => +Old_Comp)))),
                        Pred      => New_Conditional
                          (Condition => +New_Array_Range_Expr
                               (+Index, +Old_Name, EW_Pred, 1),
                           Then_Part => Result));

                     --  Add the bound equality if the array is not statically
                     --  constrained.

                     if not Is_Static_Array_Type (Writes.Ty) then
                        Result := New_And_Pred
                          (Left  => New_Bounds_Equality
                             (Left_Arr  => Old_Name,
                              Right_Arr => New_Name,
                              Dim       => 1),
                           Right => Result);
                     end if;
                  end;

                  --  Generate the top-level conditional if necessary (see
                  --  Needs_Default).

                  if Needs_Default then
                     Result := New_Conditional
                       (Condition => Other_Choices
                          (Values  => Writes.Values,
                           Indices => Indices),
                        Then_Part => New_Comparison
                          (Symbol => Why_Eq,
                           Left   => New_Name,
                           Right  => Insert_Simple_Conversion
                             (Expr           => Old_Name,
                              To             => Get_Type (+New_Name),
                              Force_No_Slide => True)),
                        Else_Part => Result);
                  end if;
            end case;

            return Result;
         end Generate_Aggregate_Value_Internal;

         ----------------------------------------
         -- Generate_Values_For_Record_Updates --
         ----------------------------------------

         function Generate_Values_For_Record_Updates
           (Writes      : Write_Status;
            New_Name    : W_Term_Id;
            Old_Name    : W_Term_Id;
            Root_Values : Constrained_Value_Vectors.Vector;
            Indices     : W_Identifier_Array)
            return W_Pred_Id
         is
            Conjuncts : W_Pred_Array
              (1 .. Integer (Writes.Component_Status.Length));
            Top       : Natural := 0;

         begin
            --  Go over the updated components to compute their predicate and
            --  store it inside Conjuncts.

            for Position in Writes.Component_Status.Iterate loop
               Top := Top + 1;

               declare
                  use Write_Status_Maps;
                  Comp        : constant Entity_Id := Key (Position);
                  Comp_Writes : constant Write_Status_Access :=
                    Element (Position);

               begin
                  --  If the component is a record and its value is not
                  --  entirely written, only consider its updated components.

                  if Comp_Writes.Kind = Record_Components
                    and then not Has_Additional_Writes
                      (Writes.Values, Comp_Writes.Values)
                  then
                     Conjuncts (Top) :=
                       Generate_Values_For_Record_Updates
                         (Writes      => Comp_Writes.all,
                          New_Name    => New_Ada_Record_Access
                            (Name  => New_Name,
                             Field => Comp,
                             Ty    => Writes.Ty),
                          Old_Name    => New_Ada_Record_Access
                            (Name  => Old_Name,
                             Field => Comp,
                             Ty    => Writes.Ty),
                          Root_Values => Root_Values,
                          Indices     => Indices);

                  --  Otherwise, the component is handled as a whole

                  else
                     Conjuncts (Top) :=
                       Generate_Aggregate_Value_Internal
                         (Writes      => Comp_Writes.all,
                          New_Name    => New_Ada_Record_Access
                            (Name  => New_Name,
                             Field => Comp,
                             Ty    => Writes.Ty),
                          Old_Name    => New_Ada_Record_Access
                            (Name  => Old_Name,
                             Field => Comp,
                             Ty    => Writes.Ty),
                          Root_Values => Root_Values,
                          Indices     => Indices);
                  end if;
               end;
            end loop;

            return New_And_Pred (Conjuncts => Conjuncts);
         end Generate_Values_For_Record_Updates;

         ---------------------
         -- New_Conditional --
         ---------------------

         function New_Conditional
           (Conditions : W_Pred_Array;
            Predicates : W_Pred_Array)
            return W_Pred_Id
         is
         begin
            if Conditions'Length = 0 then
               return Predicates (1);
            else
               return New_Conditional
                 (Condition   => Conditions (1),
                  Then_Part   => Predicates (1),
                  Elsif_Parts =>
                    (for I in 2 .. Conditions'Length =>
                         +New_Elsif (Condition => Conditions (I),
                                     Then_Part => Predicates (I))),
                  Else_Part   => Predicates (Predicates'Length));
            end if;
         end New_Conditional;

         ---------------------
         -- Transform_Value --
         ---------------------

         function Transform_Path
           (Path    : Path_Type;
            Indices : W_Identifier_Array)
            return W_Term_Id
         is
         begin
            if Path.Kind = Root then
               return +Value_Map.Element (Path.Expr);
            else
               declare
                  Prefix : constant W_Term_Id := Transform_Path
                    (Path.Prefix, Indices);
               begin
                  if Path.Kind = Record_Acc then
                     return New_Ada_Record_Access
                       (Name  => Prefix,
                        Field => Path.Field,
                        Ty    => Get_Ada_Node (+Get_Type (+Prefix)));
                  else
                     return New_Array_Access
                       (Ar    => Prefix,
                        Index => (1 => +Indices (Path.Index)));
                  end if;
               end;
            end if;
         end Transform_Path;

         -------------------
         -- Other_Choices --
         -------------------

         function Other_Choices
           (Values  : Constrained_Value_Vectors.Vector;
            Indices : W_Identifier_Array)
            return W_Pred_Id
         is
            Conjuncts : W_Pred_Array (1 .. Values.Last_Index);
            Top       : Natural := 0;

         begin
            for Val of Values loop
               if Val.Status.Kind /= Preserved then
                  Top := Top + 1;
                  Conjuncts (Top) := New_Not
                    (Right => Transform_Choices
                       (Val.Choices, Indices, Value_Map));
               end if;
            end loop;

            pragma Assert (Top /= 0);
            return New_And_Pred (Conjuncts (1 .. Top));
         end Other_Choices;

      --  Start of processing for Generate_Pred_For_Aggregate

      begin
         return Generate_Aggregate_Value_Internal
           (Writes      => Writes,
            New_Name    => New_Name,
            Old_Name    => Old_Name,
            Root_Values => Writes.Values,
            Indices     => (1 .. 0 => <>));
      end Generate_Pred_For_Aggregate;

      -------------------------------
      -- Generate_Simple_Record_Aggregate --
      -------------------------------

      function Generate_Simple_Record_Aggregate
        (Writes       : Write_Status;
         Ada_Node     : Node_Id;
         Expr         : W_Expr_Id;
         Relaxed_Init : Boolean;
         Domain       : EW_Domain;
         Params       : Transformation_Params)
         return W_Expr_Id
      is
         Assocs     : W_Field_Association_Array
           (1 .. Integer (Writes.Component_Status.Length));
         Top        : Natural := 0;
         Result     : W_Expr_Id;

         Num_Discrs : constant Natural := Count_Discriminants (Writes.Ty);
         Tmps       : W_Identifier_Array (1 .. Num_Discrs);
         Vals       : W_Expr_Array (1 .. Num_Discrs);
         Checks     : W_Statement_Sequence_Id := Void_Sequence;

      begin
         --  As discriminants may occur as bounds in types of discriminant
         --  dependent components, store them in the symbol table.

         Ada_Ent_To_Why.Push_Scope (Symbol_Table);

         if Num_Discrs > 0 then
            declare
               D : Entity_Id := First_Discriminant (Writes.Ty);
            begin
               for I in 1 .. Num_Discrs loop
                  Tmps (I) := New_Temp_Identifier
                    (Typ => EW_Abstract (Etype (D)));
                  Vals (I) := New_Ada_Record_Access
                    (Ada_Node => Empty,
                     Domain   => EW_Term,
                     Name     => Expr,
                     Field    => D,
                     Ty       => Writes.Ty);

                  Insert_Tmp_Item_For_Entity (D, Tmps (I));

                  Next_Discriminant (D);
               end loop;
               pragma Assert (No (D));
            end;
         end if;

         --  Fill the Assocs array with an association per updated component

         for Position in Writes.Component_Status.Iterate loop
            declare
               use Write_Status_Maps;
               Comp         : constant Entity_Id := Key (Position);
               C_Writes     : constant Write_Status_Access :=
                 Element (Position);
               Comp_Relaxed : constant Boolean :=
                 (if Relaxed_Init then Has_Init_Wrapper (C_Writes.Ty)
                  else Has_Relaxed_Init (C_Writes.Ty));
               W_Comp_Ty    : constant W_Type_Id := EW_Abstract
                 (C_Writes.Ty, Comp_Relaxed);
               C_Node       : Node_Id := Types.Empty;
               Res          : W_Expr_Id := Why_Empty;

            begin
               --  To locate the check, search for the first association
               --  with a non-empty Ada node.

               for C_Value of C_Writes.Values loop
                  if Present (C_Value.Ada_Node) then
                     C_Node := C_Value.Ada_Node;
                     exit;
                  end if;
               end loop;

               --  If the record has discriminants and we are in the program
               --  domain, check that selectors are present in the prefix.

               if Domain = EW_Prog and then Num_Discrs > 0 then
                  Append
                    (Checks,
                     (New_Ignore
                          (Prog => New_Ada_Record_Access
                             (Ada_Node => C_Node,
                              Name     => +Expr,
                              Field    => Key (Position),
                              Ty       => Writes.Ty))));
               end if;

               case C_Writes.Kind is

                  --  This simpler translation is only used when there are no
                  --  array indexed components in the selectors.

                  when Array_Components =>
                     raise Program_Error;

                  when Entire_Object =>

                     --  Search for a constrained value which is not preserved.
                     --  There should be exactly one and its Path should be a
                     --  direct expression.

                     for Position in C_Writes.Values.Iterate loop
                        declare
                           use Constrained_Value_Vectors;
                           C_Value : Constrained_Value renames
                             Element (Position);
                        begin
                           if C_Value.Status.Kind = Entire then
                              pragma Assert (C_Value.Status.Path.Kind = Root);

                              Res := Transform_Expr
                                (Expr          => C_Value.Status.Path.Expr,
                                 Expected_Type => W_Comp_Ty,
                                 Domain        => Domain,
                                 Params        => Params);

                              pragma Assert
                                (for all P in C_Writes.Values.Iterate =>
                                   (if P /= Position
                                    then Element (P).Status.Kind = Preserved));
                              exit;
                           end if;
                        end;
                     end loop;

                  when Record_Components =>

                     --  Call recursively Generate_Simple_Record_Aggregate on
                     --  the component's writes.

                     Res := Generate_Simple_Record_Aggregate
                       (Writes       => C_Writes.all,
                        Ada_Node     => C_Node,
                        Expr         => New_Ada_Record_Access
                          (Domain => Term_Domain (Domain),
                           Name   => Expr,
                           Field  => Comp,
                           Ty     => Writes.Ty),
                        Relaxed_Init => Comp_Relaxed,
                        Domain       => Domain,
                        Params       => Params);
               end case;

               Top := Top + 1;
               Assocs (Top) := New_Field_Association
                 (Domain => Domain,
                  Field  => To_Why_Id
                    (Comp, Rec => Writes.Ty, Relaxed_Init => Relaxed_Init),
                  Value  => Res);
            end;
         end loop;

         Result := New_Ada_Record_Update
           (Name    => Expr,
            Domain  => Domain,
            Updates => Assocs);

         --  Prepend the discriminant checks if any

         if Domain = EW_Prog and then Num_Discrs > 0 then
            Prepend (+Checks, Result);
         end if;

         --  If the target type has a direct or inherited predicate,
         --  generate a corresponding check.

         if Domain = EW_Prog and then Has_Predicates (Writes.Ty) then
            Result := +Insert_Predicate_Check (Ada_Node => Ada_Node,
                                               Check_Ty => Writes.Ty,
                                               W_Expr   => +Result);
         end if;

         --  Add bindings for discriminants

         for I in 1 .. Num_Discrs loop
            Result := New_Binding
              (Domain  => Domain,
               Name    => Tmps (I),
               Def     => Vals (I),
               Context => Result,
               Typ     => Get_Type (Result));
         end loop;

         Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

         return Result;
      end Generate_Simple_Record_Aggregate;

      ----------------------------
      -- Get_Aggregate_Elements --
      ----------------------------

      procedure Get_Aggregate_Elements
        (Writes    : Write_Status;
         Value_Map : in out Ada_Node_To_Why_Id.Map)
      is
      begin
         --  Go over the constrained values of Writes and store them in
         --  Value_Map.

         for C_Value of Writes.Values loop
            if C_Value.Status.Kind = Entire
              and then C_Value.Status.Path.Kind = Root
            then
               declare
                  W_Id : constant W_Identifier_Id := New_Temp_Identifier
                    (Typ       => EW_Abstract
                       (Writes.Ty,
                        Expr_Has_Relaxed_Init
                          (C_Value.Status.Path.Expr, No_Eval => False)),
                     Base_Name => "val");
               begin
                  Value_Map.Insert (C_Value.Status.Path.Expr, W_Id);
               end;
            end if;
         end loop;

         case Writes.Kind is
            when Entire_Object =>
               null;

            when Array_Components =>

               --  Go over the choice indexes and store them in Index_Map

               declare
                  Idx_Typ : constant W_Type_Id :=
                    Nth_Index_Rep_Type_No_Bool (Writes.Ty, 1);
               begin
                  for C_Value of Writes.Content_Status.Values loop
                     declare
                        Index : constant Node_Id :=
                          C_Value.Choices (C_Value.Size);
                     begin
                        if Present (Index) then
                           Value_Map.Insert
                             (Index,
                              New_Temp_Identifier
                                (Typ => Idx_Typ, Base_Name => "index"));
                        end if;
                     end;
                  end loop;
               end;

               Get_Aggregate_Elements
                 (Writes.Content_Status.all, Value_Map);

            when Record_Components =>
               for C_Writes of Writes.Component_Status loop
                  Get_Aggregate_Elements (C_Writes.all, Value_Map);
               end loop;
         end case;
      end Get_Aggregate_Elements;

      --------------------------------
      -- Is_Simple_Record_Aggregate --
      --------------------------------

      function Is_Simple_Record_Aggregate
        (Writes : Write_Status)
         return Boolean
      is
      begin
         case Writes.Kind is
            when Entire_Object =>
               return True;

            when Array_Components =>
               return False;

            when Record_Components =>
               return (for all C_Writes of Writes.Component_Status =>
                          Is_Simple_Record_Aggregate (C_Writes.all));
         end case;
      end Is_Simple_Record_Aggregate;

      ----------------------
      -- Transform_Choice --
      ----------------------

      function Transform_Choice
        (Choice    : Node_Id;
         Index     : W_Identifier_Id;
         Value_Map : Ada_Node_To_Why_Id.Map)
         return W_Pred_Id
      is
      begin
         if No (Choice) then
            return True_Pred;
         else
            return New_Comparison
              (Symbol => Why_Eq,
               Left   => +Index,
               Right  => +Value_Map.Element (Choice));
         end if;
      end Transform_Choice;

      -----------------------
      -- Transform_Choices --
      -----------------------

      function Transform_Choices
        (Choices   : Choice_Array;
         Indices   : W_Identifier_Array;
         Value_Map : Ada_Node_To_Why_Id.Map)
         return W_Pred_Id
      is
         Conjuncts : W_Pred_Array (Choices'Range);

      begin
         if Choices'Length = 0 then
            return True_Pred;
         end if;

         for I in Choices'Range loop
            Conjuncts (I) := Transform_Choice
              (Choices (I), Indices (I), Value_Map);
         end loop;

         return New_And_Pred (Conjuncts);
      end Transform_Choices;

      Pref     : constant Node_Id := Expression (Expr);
      Pref_Typ : constant Entity_Id := Retysp (Etype (Pref));
      W_Pref   : W_Expr_Id;
      Writes   : Write_Status_Access;
      Elements : Node_Vectors.Vector;
      T        : W_Expr_Id;

   --  Start of processing for Transform_Deep_Delta_Aggregate

   begin
      W_Pref := Transform_Expr
        (Domain        => Domain,
         Expr          => Pref,
         Params        => Params,
         Expected_Type => EW_Abstract
           (Pref_Typ, Relaxed_Init =>
                Expr_Has_Relaxed_Init (Pref, No_Eval => False)));

      W_Pref := New_Temp_For_Expr (W_Pref, Has_Discriminants (Pref_Typ));

      Create (Pref_Typ, Writes);

      declare
         Assoc  : Node_Id := First (Component_Associations (Expr));
         Choice : Node_Id;
      begin
         while Present (Assoc) loop
            Choice := First (Choice_List (Assoc));

            while Present (Choice) loop
               Insert_Association
                 (Writes      => Writes,
                  Deep_Access => Choice,
                  Value       => Expression (Assoc));

               --  Collect both the expression and the indexes if any

               declare
                  Pref : Node_Id := Choice;
               begin
                  while not Is_Root_Prefix_Of_Deep_Choice (Pref) loop
                     if Nkind (Pref) in N_Indexed_Component then
                        Elements.Append (First (Expressions (Pref)));
                     end if;
                     Pref := Prefix (Pref);
                  end loop;

                  if Is_Array_Type (Pref_Typ) then
                     Elements.Append (Pref);
                  end if;
               end;
               Elements.Append (Expression (Assoc));

               Next (Choice);
            end loop;

            Next (Assoc);
         end loop;
      end;

      T := Generate_Deep_Delta_Aggregate
        (Writes       => Writes.all,
         Elements     => Elements,
         Ada_Node     => Expr,
         Expr         => W_Pref,
         Relaxed_Init => Expr_Has_Relaxed_Init (Expr, No_Eval => False),
         Domain       => Domain,
         Params       => Params);

      Finalize (Writes);

      T := Binding_For_Temp
        (Ada_Node => Expr,
         Domain   => Domain,
         Tmp      => W_Pref,
         Context  => T);

      return T;
   end Transform_Deep_Delta_Aggregate;

end Gnat2Why.Expr.Aggregates;
