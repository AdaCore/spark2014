------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - B I N D E R S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2025, AdaCore                     --
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

with Flow_Utility;           use Flow_Utility;
with Gnat2Why.Util;          use Gnat2Why.Util;
with Namet;                  use Namet;
with SPARK_Util.Subprograms; use SPARK_Util.Subprograms;
with SPARK_Util.Types;       use SPARK_Util.Types;
with Why.Atree.Modules;      use Why.Atree.Modules;
with Why.Gen.Arrays;         use Why.Gen.Arrays;
with Why.Gen.Expr;           use Why.Gen.Expr;
with Why.Gen.Init;           use Why.Gen.Init;
with Why.Gen.Names;          use Why.Gen.Names;
with Why.Gen.Pointers;       use Why.Gen.Pointers;
with Why.Gen.Records;        use Why.Gen.Records;
with Why.Images;             use Why.Images;
with Why.Inter;              use Why.Inter;

package body Why.Gen.Binders is

   function New_Binders
     (Domain : EW_Domain; Binders : Binder_Array) return W_Binder_Array;

   function New_Constant_Record_Binders
     (Binders : Binder_Array) return W_Record_Binder_Array;

   ----------------------------
   -- Concurrent_Self_Binder --
   ----------------------------

   function Concurrent_Self_Binder
     (Ty : Entity_Id; Mutable : Boolean := True) return Binder_Type is
   begin
      return
        Binder_Type'
          (Ada_Node => Ty,
           B_Name   => Concurrent_Self_Ident (Ty),
           B_Ent    => Null_Entity_Name,
           Mutable  => Mutable,
           Labels   => <>);
   end Concurrent_Self_Binder;

   ---------------------------
   -- Concurrent_Self_Ident --
   ---------------------------

   function Concurrent_Self_Ident (Ty : Entity_Id) return W_Identifier_Id is
      Typ : constant W_Type_Id :=
        (if Entity_In_SPARK (Ty) then Type_Of_Node (Ty) else EW_Private_Type);
   begin
      return New_Identifier (Name => "self__", Typ => Typ);
   end Concurrent_Self_Ident;

   ----------------------------------
   -- Concurrent_Self_Move_Tree_Id --
   ----------------------------------

   function Concurrent_Self_Move_Tree_Id
     (Ty : Entity_Id) return W_Identifier_Id
   is
      Typ : constant W_Type_Id := Get_Move_Tree_Type (Ty);
   begin
      return New_Identifier (Name => "self__move_tree__", Typ => Typ);
   end Concurrent_Self_Move_Tree_Id;

   ---------------------------
   -- Effects_Append_Binder --
   ---------------------------

   procedure Effects_Append_Binder (Eff : W_Effects_Id; Binder : Item_Type) is
   begin
      if Binder.Valid.Present and then Item_Is_Mutable (Binder) then
         Effects_Append (Eff, Binder.Valid.Id);
      end if;

      case Binder.Kind is
         when Regular | Concurrent_Self =>
            if Binder.Main.Mutable then
               Effects_Append (Eff, Binder.Main.B_Name);
            end if;

         when UCArray                   =>
            Effects_Append (Eff, Binder.Content.B_Name);

         when Pointer                   =>
            if Binder.Mutable then
               Effects_Append (Eff, Binder.Value.B_Name);
               Effects_Append (Eff, Binder.Is_Null);
            elsif Binder.Value.Mutable then
               Effects_Append (Eff, Binder.Value.B_Name);
            end if;

         when DRecord                   =>
            if Binder.Fields.Present then
               Effects_Append (Eff, Binder.Fields.Binder.B_Name);
            end if;
            if Binder.Discrs.Present and then Binder.Discrs.Binder.Mutable then
               Effects_Append (Eff, Binder.Discrs.Binder.B_Name);
            end if;

         when Subp                      =>
            raise Program_Error;
      end case;
   end Effects_Append_Binder;

   ----------------------------
   -- Get_Ada_Node_From_Item --
   ----------------------------

   function Get_Ada_Node_From_Item (B : Item_Type) return Node_Id is
   begin
      case B.Kind is
         when Regular | Concurrent_Self =>
            return B.Main.Ada_Node;

         when DRecord                   =>
            if B.Fields.Present then
               return B.Fields.Binder.Ada_Node;
            else
               return B.Discrs.Binder.Ada_Node;
            end if;

         when UCArray                   =>
            return B.Content.Ada_Node;

         when Pointer                   =>
            return B.Value.Ada_Node;

         when Subp                      =>
            raise Program_Error;
      end case;
   end Get_Ada_Node_From_Item;

   ----------------------------
   -- Get_Ada_Type_From_Item --
   ----------------------------

   function Get_Ada_Type_From_Item (B : Item_Type) return Entity_Id is
   begin
      case B.Kind is
         when Subp              =>
            raise Program_Error;

         when Regular | UCArray =>
            if Get_Type_Kind (Get_Why_Type_From_Item (B))
               in EW_Split | EW_Abstract
            then
               return Get_Ada_Node (+Get_Why_Type_From_Item (B));
            elsif Present (Get_Ada_Node_From_Item (B)) then
               return Etype (Get_Ada_Node_From_Item (B));
            else
               return Empty;
            end if;

         when Concurrent_Self   =>
            return B.Main.Ada_Node;

         when DRecord           =>
            return B.Typ;

         when Pointer           =>
            return B.P_Typ;
      end case;
   end Get_Ada_Type_From_Item;

   ---------------------------
   -- Get_Args_From_Binders --
   ---------------------------

   function Get_Args_From_Binders
     (Binders : Binder_Array; Ref_Allowed : Boolean) return W_Expr_Array
   is
      Args : W_Expr_Array (1 .. Binders'Length);
      I    : Positive := 1;
   begin
      for B of Binders loop
         if Ref_Allowed and then B.Mutable then
            Args (I) :=
              New_Deref (Right => B.B_Name, Typ => Get_Typ (B.B_Name));
         else
            Args (I) := +B.B_Name;
         end if;
         I := I + 1;
      end loop;
      return Args;
   end Get_Args_From_Binders;

   -----------------------------
   -- Get_Args_From_Variables --
   -----------------------------

   function Get_Args_From_Variables
     (Variables : Flow_Id_Sets.Set; Ref_Allowed : Boolean) return W_Expr_Array
   is (Get_Args_From_Binders
         (To_Binder_Array
            (Get_Binders_From_Variables (Variables), Keep_Const => Keep),
          Ref_Allowed));

   ---------------------------------------
   -- Get_Binders_From_Contextual_Nodes --
   ---------------------------------------

   function Get_Binders_From_Contextual_Nodes
     (Contextual_Nodes : Node_Sets.Set) return Item_Array
   is
      Binders : Item_Array (1 .. Natural (Contextual_Nodes.Length));
      I       : Positive := 1;
   begin
      for N of Contextual_Nodes loop
         case Nkind (N) is
            when N_Target_Name         =>
               pragma Assert (Target_Name /= Why_Empty);
               Binders (I) :=
                 Mk_Tmp_Item_Of_Entity
                   (E => Empty, Id => Target_Name, Mutable => False);

            when N_Attribute_Reference =>
               if Attribute_Name (N) = Name_Old then
                  Binders (I) :=
                    Mk_Tmp_Item_Of_Entity
                      (E       => Empty,
                       Id      => Name_For_Old (Prefix (N)),
                       Mutable => False);
               else
                  pragma Assert (Attribute_Name (N) = Name_Loop_Entry);
                  Binders (I) :=
                    Mk_Tmp_Item_Of_Entity
                      (E       => Empty,
                       Id      => Name_For_Loop_Entry (N),
                       Mutable => False);
               end if;

            when others                =>
               pragma Assert (Nkind (N) = N_Defining_Identifier);
               Binders (I) := Ada_Ent_To_Why.Element (Symbol_Table, N);
         end case;
         I := I + 1;
      end loop;
      return Binders;
   end Get_Binders_From_Contextual_Nodes;

   ---------------------------------
   -- Get_Binders_From_Expression --
   ---------------------------------

   function Get_Binders_From_Expression (Expr : Node_Id) return Item_Array is
      Variables : constant Flow_Id_Sets.Set :=
        Get_Variables_For_Proof (Expr, Expr);

   begin
      pragma Assert (if Is_Static_Expression (Expr) then Variables.Is_Empty);
      return Get_Binders_From_Variables (Variables);
   end Get_Binders_From_Expression;

   --------------------------------
   -- Get_Binders_From_Variables --
   --------------------------------

   function Get_Binders_From_Variables
     (Variables : Flow_Id_Sets.Set; Ignore_Self : Boolean := False)
      return Item_Array
   is
      Binders : Item_Array (1 .. Natural (Variables.Length));
      I       : Positive := 1;
   begin
      for F of Variables loop
         declare
            V       : constant Entity_Name := To_Name (F);
            Use_Ent : constant Boolean := F.Kind = Direct_Mapping;
            Entity  : constant Entity_Id :=
              (if Use_Ent then Get_Direct_Mapping_Id (F) else Empty);

            C : constant Ada_Ent_To_Why.Cursor :=
              (if Use_Ent
               then Ada_Ent_To_Why.Find (Symbol_Table, Entity)
               else Ada_Ent_To_Why.Find (Symbol_Table, F.Name));

         begin
            --  For protected types, include a reference to self

            if Use_Ent and then Is_Type (Entity) then

               --  Do nothing if the entity is a reference to a concurrent type
               --  and they are ignored.

               if Ignore_Self then
                  null;
               elsif Is_Protected_Type (Entity) then
                  declare
                     Prot_Ty : constant Entity_Id :=
                       (if Is_Type (Entity)
                        then Entity
                        else Enclosing_Concurrent_Type (Entity));
                  begin
                     Binders (I) :=
                       Item_Type'
                         (Kind     => Concurrent_Self,
                          Local    => True,
                          Init     => <>,
                          Is_Moved => <>,
                          Valid    => <>,
                          Main     => Concurrent_Self_Binder (Prot_Ty));
                     I := I + 1;
                  end;
               end if;

            --  If there is an existing binder for this entity use it

            elsif Ada_Ent_To_Why.Has_Element (C) then
               Binders (I) := Ada_Ent_To_Why.Element (C);
               I := I + 1;

            --  Otherwise, F is an opaque name of a flow effect. Construct a
            --  dummy binder with the appropriate name.

            else
               pragma Assert (not Use_Ent and then Is_Opaque_For_Proof (F));

               Binders (I) :=
                 (Regular,
                  Local    => False,
                  Init     => <>,
                  Is_Moved => <>,
                  Valid    => <>,
                  Main     =>
                    (Ada_Node => Empty,
                     B_Name   => To_Why_Id (V, Local => False),
                     B_Ent    => V,
                     Mutable  => True,
                     Labels   => <>));
               I := I + 1;
            end if;
         end;
      end loop;

      return Binders (1 .. I - 1);
   end Get_Binders_From_Variables;

   -----------------------------
   -- Get_Init_Id_From_Object --
   -----------------------------

   function Get_Init_Id_From_Object
     (Obj : Entity_Id; Ref_Allowed : Boolean) return W_Expr_Id
   is
      C    : constant Ada_Ent_To_Why.Cursor :=
        Ada_Ent_To_Why.Find (Symbol_Table, Obj);
      Item : Item_Type;
   begin
      if Ada_Ent_To_Why.Has_Element (C) then
         Item := Ada_Ent_To_Why.Element (C);
         if Item.Init.Present then
            if Ref_Allowed then
               return
                 New_Deref
                   (Right => Item.Init.Id, Typ => Get_Typ (Item.Init.Id));
            else
               return +Item.Init.Id;
            end if;
         end if;
      end if;
      return Why_Empty;
   end Get_Init_Id_From_Object;

   ------------------------------------------
   -- Get_Localized_Binders_From_Variables --
   ------------------------------------------

   function Get_Localized_Binders_From_Variables
     (Variables      : Flow_Id_Sets.Set;
      Ignore_Self    : Boolean := False;
      Suffix         : String := "";
      Only_Variables : Boolean := True) return Item_Array is
   begin
      return
         Items : Item_Array :=
           Get_Binders_From_Variables (Variables, Ignore_Self => Ignore_Self)
      do
         Localize_Binders
           (Binders        => Items,
            Suffix         => Suffix,
            Only_Variables => Only_Variables);
      end return;
   end Get_Localized_Binders_From_Variables;

   ----------------------------
   -- Get_Valid_Id_From_Item --
   ----------------------------

   function Get_Valid_Id_From_Item
     (Item : Item_Type; Ref_Allowed : Boolean) return W_Term_Id is
   begin
      if Item.Valid.Present then
         if Item_Is_Mutable (Item) and then Ref_Allowed then
            return
              New_Deref
                (Right => Item.Valid.Id, Typ => Get_Typ (Item.Valid.Id));
         else
            return +Item.Valid.Id;
         end if;
      end if;
      return Why_Empty;
   end Get_Valid_Id_From_Item;

   ------------------------------
   -- Get_Valid_Id_From_Object --
   ------------------------------

   function Get_Valid_Id_From_Object
     (Obj : Entity_Id; Ref_Allowed : Boolean) return W_Term_Id
   is
      C : constant Ada_Ent_To_Why.Cursor :=
        Ada_Ent_To_Why.Find (Symbol_Table, Obj);
   begin
      if Ada_Ent_To_Why.Has_Element (C) then
         return
           Get_Valid_Id_From_Item (Ada_Ent_To_Why.Element (C), Ref_Allowed);
      end if;
      return Why_Empty;
   end Get_Valid_Id_From_Object;

   ----------------------------
   -- Get_Why_Type_From_Item --
   ----------------------------

   function Get_Why_Type_From_Item (B : Item_Type) return W_Type_Id is
   begin
      case B.Kind is
         when Regular | Concurrent_Self =>
            return Get_Typ (B.Main.B_Name);

         when DRecord                   =>

            --  To know if we should use the wrapper type, see if the
            --  fields component comes from the wrapper module.

            declare
               Relaxed_Init : constant Boolean :=
                 (if B.Fields.Present and Has_Init_Wrapper (B.Typ)
                  then
                    Get_Module (Get_Name (Get_Typ (B.Fields.Binder.B_Name)))
                    = E_Module (B.Typ, Init_Wrapper)
                  else False);
            begin
               return EW_Abstract (B.Typ, Relaxed_Init => Relaxed_Init);
            end;

         when UCArray                   =>
            declare
               Typ : constant W_Type_Id := Get_Typ (B.Content.B_Name);
            begin
               pragma Assert (Get_Type_Kind (Typ) = EW_Split);
               return
                 EW_Abstract (Get_Ada_Node (+Typ), Get_Relaxed_Init (Typ));
            end;

         when Pointer                   =>

            --  Use the wrapper type if either we have an init field or if the
            --  designated value is of a wrapper type when the designated type
            --  is not itself annotated with Relaxed_Initialization.

            declare
               Des_Ty       : constant Entity_Id :=
                 Directly_Designated_Type (B.P_Typ);
               Relaxed_Init : constant Boolean :=
                 B.Init.Present
                 or else
                   (Has_Init_Wrapper (B.P_Typ)
                    and then not Has_Relaxed_Init (Des_Ty)
                    and then Get_Relaxed_Init (Get_Typ (B.Value.B_Name)));
            begin
               return EW_Abstract (B.P_Typ, Relaxed_Init => Relaxed_Init);
            end;

         when Subp                      =>
            raise Program_Error;

      end case;
   end Get_Why_Type_From_Item;

   -----------------------
   -- Item_Array_Length --
   -----------------------

   function Item_Array_Length
     (Arr                   : Item_Array;
      Keep_Const            : Handling := Local_Only;
      Ignore_Init_And_Valid : Boolean := False) return Natural
   is
      function Keep_Local (Is_Local : Boolean) return Boolean
      is (case Keep_Const is
            when Keep       => True,
            when Local_Only => Is_Local,
            when Erase      => False);

      Count : Natural := 0;
   begin
      for Index in Arr'Range loop
         declare
            B : constant Item_Type := Arr (Index);
         begin
            if not Ignore_Init_And_Valid then
               if B.Init.Present then
                  Count := Count + 1;
               end if;

               if B.Valid.Present
                 and then (Item_Is_Mutable (B) or else Keep_Local (B.Local))
               then
                  Count := Count + 1;
               end if;
            end if;

            case B.Kind is
               when Regular | Concurrent_Self =>
                  if Keep_Local (B.Local) or else B.Main.Mutable then
                     Count := Count + 1;
                  end if;

               when Pointer                   =>
                  pragma Assert (B.Value.Mutable);
                  if B.Mutable or else Keep_Local (B.Local) then
                     Count := Count + 2;
                  else
                     Count := Count + 1;
                  end if;

               when UCArray                   =>
                  pragma Assert (B.Content.Mutable);
                  if Keep_Local (B.Local) then
                     Count := Count + 1 + 2 * B.Dim;
                  else
                     Count := Count + 1;
                  end if;

               when DRecord                   =>

                  if B.Discrs.Present
                    and then
                      (Keep_Local (B.Local) or else B.Discrs.Binder.Mutable)
                  then
                     Count := Count + 1;
                  end if;

                  if B.Fields.Present
                    and then
                      (Keep_Local (B.Local) or else B.Fields.Binder.Mutable)
                  then
                     Count := Count + 1;
                  end if;

                  if Keep_Local (B.Local) and then B.Constr.Present then
                     Count := Count + 1;
                  end if;

                  if Keep_Local (B.Local) and then B.Tag.Present then
                     Count := Count + 1;
                  end if;

               when Subp                      =>
                  raise Program_Error;
            end case;
         end;
      end loop;
      return Count;
   end Item_Array_Length;

   ---------------------
   -- Item_Is_Mutable --
   ---------------------

   function Item_Is_Mutable (B : Item_Type) return Boolean is
   begin
      case B.Kind is
         when Regular | Concurrent_Self   =>
            return B.Main.Mutable;

         when UCArray | DRecord | Pointer =>
            return True;

         when Subp                        =>
            raise Program_Error;
      end case;
   end Item_Is_Mutable;

   ----------------------
   -- Localize_Binders --
   ----------------------

   procedure Localize_Binders
     (Binders        : in out Item_Array;
      Suffix         : String := "";
      Only_Variables : Boolean := True)
   is

      function Local_Name (Name : W_Identifier_Id) return W_Identifier_Id;
      --  Compute a local name for Name.
      --  Return Module___Namespace___Symbol___Suffix.

      ----------------
      -- Local_Name --
      ----------------

      function Local_Name (Name : W_Identifier_Id) return W_Identifier_Id is
         Module    : constant W_Module_Id := Get_Module (Get_Name (Name));
         Namespace : constant Symbol := Get_Namespace (Get_Name (Name));
         L_Name    : constant String :=
           (if Module = Why_Empty then "" else Img (Get_Name (Module)) & "___")
           & (if Namespace = No_Symbol then "" else Img (Namespace) & "___")
           & Img (Get_Symb (Get_Name (Name)))
           & "___"
           & Suffix;
      begin
         return
           New_Identifier
             (Ada_Node => Get_Ada_Node (+Name),
              Domain   => Get_Domain (+Name),
              Name     =>
                New_Name
                  (Ada_Node => Get_Ada_Node (+Get_Name (Name)),
                   Symb     => NID (L_Name),
                   Module   => Why_Empty,
                   Infix    => Get_Infix (Get_Name (Name))),
              Typ      => Get_Typ (Name),
              Labels   => Get_Labels (Name));
      end Local_Name;

      --  Start of processing for Localize_Binders

   begin
      for B of Binders loop

         --  If the B is already local and no suffix is provided, there is
         --  nothing to do.

         if Suffix /= "" or else not B.Local then

            --  The Init field is always mutable when present

            if B.Init.Present then
               B.Init.Id := Local_Name (B.Init.Id);
            end if;

            --  The Valid field is only mutable if Mutable is True

            if B.Valid.Present
              and then (Item_Is_Mutable (B) or else not Only_Variables)
            then
               B.Valid.Id := Local_Name (B.Valid.Id);
            end if;

            case B.Kind is
               when Concurrent_Self =>
                  --  Concurrent self is already local

                  pragma Assert (Suffix = "");
                  null;

               when Regular         =>
                  if B.Main.Mutable or else not Only_Variables then
                     B.Main.B_Name := Local_Name (B.Main.B_Name);
                  end if;

               when UCArray         =>
                  pragma Assert (B.Content.Mutable);
                  B.Content.B_Name := Local_Name (B.Content.B_Name);

                  if not Only_Variables then
                     for Dim_Index in 1 .. B.Dim loop
                        B.Bounds (Dim_Index).First :=
                          Local_Name (B.Bounds (Dim_Index).First);
                        B.Bounds (Dim_Index).Last :=
                          Local_Name (B.Bounds (Dim_Index).Last);
                     end loop;
                  end if;

               when Pointer         =>
                  pragma Assert (B.Value.Mutable);
                  B.Value.B_Name := Local_Name (B.Value.B_Name);

                  if B.Mutable or else not Only_Variables then
                     B.Is_Null := Local_Name (B.Is_Null);
                  end if;

               when DRecord         =>
                  if B.Discrs.Present
                    and then
                      (B.Discrs.Binder.Mutable or else not Only_Variables)
                  then
                     B.Discrs.Binder.B_Name :=
                       Local_Name (B.Discrs.Binder.B_Name);
                  end if;

                  if B.Fields.Present
                    and then
                      (B.Fields.Binder.Mutable or else not Only_Variables)
                  then
                     B.Fields.Binder.B_Name :=
                       Local_Name (B.Fields.Binder.B_Name);
                  end if;

                  if not Only_Variables and then B.Constr.Present then
                     B.Constr.Id := Local_Name (B.Constr.Id);
                  end if;

                  if not Only_Variables and then B.Tag.Present then
                     B.Tag.Id := Local_Name (B.Tag.Id);
                  end if;

               when Subp            =>
                  raise Program_Error;
            end case;
            B.Local := B.Local or not Only_Variables;
         end if;
      end loop;
   end Localize_Binders;

   -----------------------
   -- Mk_Item_Of_Entity --
   -----------------------

   function Mk_Item_Of_Entity
     (E           : Entity_Id;
      Local       : Boolean := False;
      In_Fun_Decl : Boolean := False;
      Hide_Info   : Boolean := False) return Item_Type
   is
      Use_Ty : constant Entity_Id :=
        (if not In_Fun_Decl
           --  test when it is safe to call Actual_Subtype
           and then
             (Ekind (E) in E_Constant | E_Variable or else Is_Formal (E))
           and then Is_Mutable_In_Why (E)
           and then Present (Actual_Subtype (E))
           and then Entity_In_SPARK (Actual_Subtype (E))
         then Actual_Subtype (E)
         else Etype (E));
      --  If we are not in a function declaration, we use the actual subtype
      --  for the parameter if one is provided.

      Spec_Ty          : constant Entity_Id :=
        (if Is_Type (Use_Ty) and then Is_Class_Wide_Type (Use_Ty)
         then Get_Specific_Type_From_Classwide (Use_Ty)
         else Use_Ty);
      Ty               : constant Entity_Id :=
        (if Is_Type (Spec_Ty) then Retysp (Spec_Ty) else Spec_Ty);
      Needs_Init_Flag  : constant Boolean :=
        Is_Object (E)
        and then Is_Mutable_In_Why (E)
        and then Is_Elementary_Type (Ty)
        and then Obj_Has_Relaxed_Init (E)
        and then Ekind (E) in E_Variable | E_Out_Parameter;
      --  We only need an initialization flag for variables and out parameters
      --  of elementary types.
      Needs_Valid_Flag : constant Boolean := Is_Potentially_Invalid (E);
      --  We only need a validity flag for potentially invalid objects

      function New_Init_Id (Name : W_Identifier_Id) return Opt_Id
      is (if Needs_Init_Flag
          then (Present => True, Id => Init_Append (Name))
          else (Present => False));

      function New_Is_Moved_Id (Name : W_Identifier_Id) return Opt_Id
      is (if In_Fun_Decl
            or else Ekind (E) not in E_Constant | E_Variable | Formal_Kind
            or else not Is_Mutable_In_Why (E)
            or else not Contains_Allocated_Parts (Ty)
            or else
              (Is_Anonymous_Access_Type (Ty)
               and then
                 (Is_Access_Constant (Ty)
                  or else
                    not Contains_Allocated_Parts
                          (Directly_Designated_Type (Ty))))
          then (Present => False)
          elsif Is_Anonymous_Access_Type (Ty)
          then
            (Present => True,
             Id      =>
               Is_Moved_Append
                 (Name, Get_Move_Tree_Type (Directly_Designated_Type (Ty))))
          else
            (Present => True,
             Id      => Is_Moved_Append (Name, Get_Move_Tree_Type (Ty))));
      --  Create an identifier for the move tree of E if it can be moved. No
      --  need for move trees in function declarations.

      function New_Valid_Id (Name : W_Identifier_Id) return Opt_Id
      is (if Needs_Valid_Flag
          then
            (Present => True,
             Id      => Valid_Append (Name, Get_Validity_Tree_Type (Ty)))
          else (Present => False));

   begin
      --  For procedures, use a regular binder

      --  For subprograms, store the name for all possible variants. For
      --  functions, also store the name to be used in logic. If Hide_Info is
      --  True, use the appropriate symbol in the program domain.

      if Ekind (E) in E_Procedure | E_Entry | E_Function then
         declare
            Typ            : constant W_Type_Id :=
              (if Ekind (E) /= E_Function
               then Why_Empty
               elsif Is_Potentially_Invalid (E)
               then Validity_Wrapper_Type (Etype (E))
               else Type_Of_Node (E));
            For_Prog       : W_Identifier_Id;
            For_Logic      : Opt_Id;
            Refine_Prog    : Opt_Id;
            Dispatch_Prog  : Opt_Id;
            Dispatch_Logic : Opt_Id;
         begin
            For_Prog := To_Why_Id (E, Typ => Typ, Hide_Info => Hide_Info);

            if Ekind (E) = E_Function then
               For_Logic :=
                 (Present => True,
                  Id      => To_Why_Id (E, Typ => Typ, Domain => EW_Term));
            end if;

            if Is_Dispatching_Operation (E)
              and then not Is_Hidden_Dispatching_Operation (E)
            then
               Dispatch_Prog :=
                 (Present => True,
                  Id      => To_Why_Id (E, Typ => Typ, Selector => Dispatch));

               if Ekind (E) = E_Function then
                  Dispatch_Logic :=
                    (Present => True,
                     Id      =>
                       To_Why_Id
                         (E,
                          Typ      => Typ,
                          Domain   => EW_Term,
                          Selector => Dispatch));
               end if;
            end if;

            if Has_Refinement (E) then
               Refine_Prog :=
                 (Present => True,
                  Id      =>
                    To_Why_Id
                      (E,
                       Typ       => Typ,
                       Selector  => Refine,
                       Hide_Info => Hide_Info));
            end if;

            return
              (Subp,
               False,
               Init           => <>,
               Is_Moved       => <>,
               Valid          => <>,
               For_Logic      => For_Logic,
               For_Prog       => For_Prog,
               Refine_Prog    => Refine_Prog,
               Dispatch_Logic => Dispatch_Logic,
               Dispatch_Prog  => Dispatch_Prog);
         end;

      --  If E is in SPARK, decide whether it should be split into multiple
      --  objects in Why3 or not.

      elsif Entity_In_SPARK (Ty)
        and then Is_Array_Type (Ty)
        and then not Is_Static_Array_Type (Ty)
        and then Is_Mutable_In_Why (E)
        and then Ekind (E) /= E_Loop_Parameter
      then

         --  Binders for mutable unconstrained array parameters and objects are
         --  declared in split form to preserve the bounds through loops and
         --  procedure calls. That is:
         --    A : UCArray (Index range <>);
         --  should be translated as:
         --    a : ref __split, a__first : Index'Base, a__last : Index'Base
         --  and
         --    procedure P (A : in out UCArray);
         --  should be translated as:
         --    val p (a : ref __split, a__first : rep, a__last : rep)

         declare
            Typ    : constant W_Type_Id :=
              EW_Split (Ty, Relaxed_Init => Obj_Has_Relaxed_Init (E));
            Name   : constant W_Identifier_Id :=
              To_Why_Id (E => E, Typ => Typ, Local => Local);
            Binder : constant Binder_Type :=
              Binder_Type'
                (Ada_Node => E,
                 B_Name   => Name,
                 B_Ent    => Null_Entity_Name,
                 Mutable  => Is_Mutable_In_Why (E),
                 Labels   => <>);
            Dim    : constant Positive := Positive (Number_Dimensions (Ty));
            Bounds : Array_Bounds;
            Index  : Node_Id := First_Index (Ty);
         begin
            for D in 1 .. Dim loop
               declare
                  Index_Typ : constant W_Type_Id :=
                    EW_Abstract (Base_Type (Etype (Index)));
               begin
                  Bounds (D).First :=
                    Attr_Append (Name, Attribute_First, D, Index_Typ);
                  Bounds (D).Last :=
                    Attr_Append (Name, Attribute_Last, D, Index_Typ);
                  Next_Index (Index);
               end;
            end loop;

            return
              (Kind     => UCArray,
               Local    => Local,
               Init     => New_Init_Id (Name),
               Is_Moved => New_Is_Moved_Id (Name),
               Valid    => New_Valid_Id (Name),
               Content  => Binder,
               Dim      => Dim,
               Bounds   => Bounds);
         end;

      elsif Entity_In_SPARK (Ty)
        and then Is_Record_Type_In_Why (Ty)
        and then not Is_Simple_Private_Type (Ty)
        --  Do not use split form for completely private types.

        and then Is_Mutable_In_Why (E)
        and then Ekind (E) /= E_Loop_Parameter
        and then Count_Why_Top_Level_Fields (Ty) > 0
      then
         declare
            Name : constant W_Identifier_Id :=
              To_Why_Id (E => E, Local => Local);
            --  This name does not correspond to a given declaration (thus, we
            --  don't give it a type). It is only used to prefix generic names
            --  of elements of the record.

            Result   : Item_Type :=
              (Kind     => DRecord,
               Local    => Local,
               Init     => New_Init_Id (Name),
               Is_Moved => New_Is_Moved_Id (Name),
               Valid    => New_Valid_Id (Name),
               Typ      => Ty,
               others   => <>);
            Unconstr : constant Boolean := Has_Mutable_Discriminants (Ty);
         begin
            if Count_Why_Regular_Fields (Ty) > 0 then
               Result.Fields :=
                 (Present => True,
                  Binder  =>
                    Binder_Type'
                      (Ada_Node => E,
                       B_Name   =>
                         Field_Append
                           (Base => Name,
                            Typ  =>
                              Field_Type_For_Fields
                                (Ty,
                                 Relaxed_Init => Obj_Has_Relaxed_Init (E))),
                       B_Ent    => Null_Entity_Name,
                       Mutable  => True,
                       Labels   => <>));
            end if;

            if Has_Discriminants (Ty) then
               Result.Discrs :=
                 (Present => True,
                  Binder  =>
                    Binder_Type'
                      (Ada_Node => E,
                       B_Name   =>
                         Discr_Append
                           (Base => Name,
                            Typ  => Field_Type_For_Discriminants (Ty)),
                       B_Ent    => Null_Entity_Name,
                       Mutable  => Unconstr,
                       Labels   => <>));
            end if;

            if Is_Assignable (E) and then Has_Defaulted_Discriminants (Ty) then
               Result.Constr :=
                 (Present => True,
                  Id      =>
                    Attr_Append
                      (Base  => Name,
                       A     => Attribute_Constrained,
                       Count => 1,
                       Typ   => EW_Bool_Type));
            end if;

            if Is_Tagged_Type (Ty) then
               Result.Tag :=
                 (Present => True,
                  Id      =>
                    Attr_Append
                      (Base  => Name,
                       A     => Attribute_Tag,
                       Count => 1,
                       Typ   => EW_Int_Type));
            end if;

            return Result;
         end;

      --  Mutable pointers are in split form

      elsif Entity_In_SPARK (Ty)
        and then Is_Access_Type (Ty)
        and then not Is_Access_Subprogram_Type (Ty)
        and then Is_Mutable_In_Why (E)
        and then Ekind (E) /= E_Loop_Parameter
      then
         declare
            Name : constant W_Identifier_Id :=
              To_Why_Id (E => E, Local => Local);
            --  This name does not correspond to a given declaration (thus, we
            --  don't give it a type). It is only used to prefix generic names
            --  of elements of the pointer.

            Des_Ty   : constant Entity_Id := Directly_Designated_Type (Ty);
            Value_Ty : constant W_Type_Id :=
              EW_Abstract
                (Des_Ty,
                 Relaxed_Init =>
                   Has_Relaxed_Init (Des_Ty) or else Obj_Has_Relaxed_Init (E));

         begin
            return
              Item_Type'
                (Kind     => Pointer,
                 Local    => Local,
                 Init     => New_Init_Id (Name),
                 Is_Moved => New_Is_Moved_Id (Name),
                 Valid    => New_Valid_Id (Name),
                 P_Typ    => Ty,
                 Mutable  => not Is_Constant_Object (E),
                 Value    =>
                   Binder_Type'
                     (Ada_Node => E,
                      B_Name   => Value_Append (Base => Name, Typ => Value_Ty),
                      B_Ent    => Null_Entity_Name,
                      Mutable  => True,
                      Labels   => <>),
                 Is_Null  =>
                   Is_Null_Append (Base => Name, Typ => EW_Bool_Type));
         end;

      else
         declare
            Typ : constant W_Type_Id :=
              (if Is_For_Loop_Parameter (E)
                 and then Is_Standard_Boolean_Type (Ty)
               then EW_Int_Type

               --  Use an init wrapper type for objects with relaxed init

               elsif Obj_Has_Relaxed_Init (E) and then not Is_Scalar_Type (Ty)
               then EW_Init_Wrapper (Type_Of_Node (Ty))

               --  Otherwise we use Why3 representation for the type

               else Type_Of_Node (Ty));

            pragma
              Assert
                (if Is_Scalar_Type (Ty) and then Obj_Has_Relaxed_Init (E)
                 then Needs_Init_Flag);
            --  Scalar types are translated as split types. If they have
            --  relaxed initialization, they should have a separate init
            --  flag.

            Name   : constant W_Identifier_Id :=
              To_Why_Id (E => E, Typ => Typ, Local => Local, No_Comp => True);
            Binder : constant Binder_Type :=
              Binder_Type'
                (Ada_Node => E,
                 B_Name   => Name,
                 B_Ent    => Null_Entity_Name,
                 Mutable  => Is_Mutable_In_Why (E),
                 Labels   => <>);
         begin
            return
              (Regular,
               Local,
               New_Init_Id (Name),
               New_Is_Moved_Id (Name),
               New_Valid_Id (Name),
               Binder);
         end;
      end if;
   end Mk_Item_Of_Entity;

   ---------------------------------
   -- New_Constant_Record_Binders --
   ---------------------------------

   function New_Constant_Record_Binders
     (Binders : Binder_Array) return W_Record_Binder_Array
   is
      Result : W_Record_Binder_Array (Binders'Range);

   begin
      for B in Binders'Range loop
         Result (B) :=
           New_Record_Binder
             (Ada_Node   => Binders (B).Ada_Node,
              Domain     => EW_Term,
              Name       => Binders (B).B_Name,
              Labels     => Binders (B).Labels,
              Arg_Type   => Get_Type (+Binders (B).B_Name),
              Is_Mutable => Binders (B).Mutable);
      end loop;

      return Result;
   end New_Constant_Record_Binders;

   ------------------------
   -- New_Defining_Axiom --
   ------------------------

   function New_Defining_Axiom
     (Ada_Node : Node_Id := Empty;
      Name     : W_Identifier_Id;
      Binders  : Binder_Array;
      Pre      : W_Pred_OId := Why_Empty;
      Def      : W_Term_Id) return W_Declaration_Id
   is
      Left       : constant W_Term_Id :=
        +New_Call (Domain => EW_Term, Name => Name, Binders => Binders);
      Equality   : W_Pred_Id;
      Node_Name  : constant String := (Img (Get_Symb (Get_Name (Name))));
      Axiom_Name : constant String :=
        (if Node_Name /= "" then Node_Name & "__" else "") & Def_Axiom;
   begin
      Equality :=
        New_Call (Name => Why_Eq, Args => (+Left, +Def), Typ => EW_Bool_Type);
      return
        New_Guarded_Axiom
          (Ada_Node => Ada_Node,
           Name     => NID (Axiom_Name),
           Binders  => Binders,
           Triggers =>
             New_Triggers
               (Triggers => (1 => New_Trigger (Terms => (1 => +Left)))),
           Pre      => Pre,
           Def      => Equality,
           Dep      => New_Axiom_Dep (Name => Name, Kind => EW_Axdep_Func));
   end New_Defining_Axiom;

   -----------------------------
   -- New_Defining_Bool_Axiom --
   -----------------------------

   function New_Defining_Bool_Axiom
     (Ada_Node : Node_Id := Empty;
      Fun_Name : String := "";
      Name     : W_Identifier_Id;
      Binders  : Binder_Array;
      Pre      : W_Pred_Id := Why_Empty;
      Def      : W_Pred_Id;
      Dep_Kind : EW_Axiom_Dep_Kind) return W_Declaration_Id
   is
      Left       : constant W_Term_Id :=
        +New_Call (Domain => EW_Term, Name => Name, Binders => Binders);
      Equality   : constant W_Pred_Id :=
        New_Call (Name => Why_Eq, Args => (+Left, +Def), Typ => EW_Bool_Type);
      Axiom_Name : constant String :=
        (if Fun_Name /= ""
         then Fun_Name & "__"
         elsif Ada_Node /= Empty
         then Short_Name (Ada_Node) & "__"
         else "")
        & Def_Axiom;
   begin
      return
        New_Guarded_Axiom
          (Ada_Node => Ada_Node,
           Name     => NID (Axiom_Name),
           Binders  => Binders,
           Triggers =>
             New_Triggers
               (Triggers => (1 => New_Trigger (Terms => (1 => +Left)))),
           Pre      => Pre,
           Def      => Equality,
           Dep      => New_Axiom_Dep (Name => Name, Kind => Dep_Kind));
   end New_Defining_Bool_Axiom;

   -----------------
   -- New_Binders --
   -----------------

   function New_Binders
     (Domain : EW_Domain; Binders : Binder_Array) return W_Binder_Array
   is

      function New_Arg_Type (Binder : Binder_Type) return W_Type_Id;

      ------------------
      -- New_Arg_Type --
      ------------------

      function New_Arg_Type (Binder : Binder_Type) return W_Type_Id is
      begin
         if Domain = EW_Prog and then Binder.Mutable then
            return New_Ref_Type (Ty => Get_Type (+Binder.B_Name));
         else
            return Get_Type (+Binder.B_Name);
         end if;
      end New_Arg_Type;

      Result : W_Binder_Array (Binders'Range);

      --  Start of processing for New_Binders

   begin
      for B in Binders'Range loop
         Result (B) :=
           New_Binder
             (Ada_Node => Binders (B).Ada_Node,
              Domain   => Domain,
              Name     => Binders (B).B_Name,
              Arg_Type => New_Arg_Type (Binders (B)));
      end loop;

      return Result;
   end New_Binders;

   --------------
   -- New_Call --
   --------------

   function New_Call
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Identifier_Id;
      Binders  : Binder_Array;
      Typ      : W_Type_Id := Why_Empty) return W_Expr_Id is
   begin
      return
        New_Call
          (Ada_Node => Ada_Node,
           Domain   => Domain,
           Name     => Name,
           Args     => Get_Args_From_Binders (Binders, False),
           Typ      => Typ);
   end New_Call;

   -----------------------
   -- New_Function_Decl --
   -----------------------

   function New_Function_Decl
     (Ada_Node    : Node_Id := Empty;
      Domain      : EW_Domain;
      Name        : W_Identifier_Id;
      Binders     : Binder_Array;
      Return_Type : W_Type_Id := Why_Empty;
      Location    : Source_Ptr;
      Labels      : Symbol_Set;
      Effects     : W_Effects_Id := New_Effects;
      Def         : W_Expr_Id := Why_Empty;
      Pre         : W_Pred_Id := True_Pred;
      Post        : W_Pred_Id := True_Pred) return W_Declaration_Id is
   begin
      return
        New_Function_Decl
          (Ada_Node    => Ada_Node,
           Domain      => Domain,
           Name        => Name,
           Labels      => Labels,
           Location    => Location,
           Binders     => New_Binders (Domain, Binders),
           Return_Type => +Return_Type,
           Def         => Def,
           Effects     => Effects,
           Pre         => Pre,
           Post        => Post);
   end New_Function_Decl;

   function New_Function_Decl
     (Ada_Node    : Node_Id := Empty;
      Domain      : EW_Domain;
      Name        : W_Identifier_Id;
      Items       : Item_Array;
      Return_Type : W_Type_Id := Why_Empty;
      Location    : Source_Ptr;
      Labels      : Symbol_Set;
      Effects     : W_Effects_Id := New_Effects;
      Def         : W_Expr_Id := Why_Empty;
      Pre         : W_Pred_Id := True_Pred;
      Post        : W_Pred_Id := True_Pred) return W_Declaration_Id
   is
      Loc_Items : Item_Array := Items;
   begin
      Localize_Binders (Loc_Items);

      return
        New_Function_Decl
          (Ada_Node    => Ada_Node,
           Domain      => Domain,
           Name        => Name,
           Labels      => Labels,
           Location    => Location,
           Binders     => To_Binder_Array (Loc_Items),
           Return_Type => +Return_Type,
           Def         => Def,
           Effects     => Effects,
           Pre         => Pre,
           Post        => Post);
   end New_Function_Decl;

   -----------------------
   -- New_Guarded_Axiom --
   -----------------------

   function New_Guarded_Axiom
     (Ada_Node : Node_Id := Empty;
      Name     : Symbol;
      Binders  : Binder_Array;
      Triggers : W_Triggers_OId := Why_Empty;
      Pre      : W_Pred_OId := Why_Empty;
      Def      : W_Pred_Id;
      Dep      : W_Axiom_Dep_OId := Why_Empty) return W_Declaration_Id
   is
      Ax_Body : constant W_Pred_Id :=
        (if Pre = Why_Empty or else Is_True_Boolean (+Pre)
         then Def
         else New_Connection (Op => EW_Imply, Left => +Pre, Right => +Def));
   begin
      return
        New_Axiom
          (Ada_Node => Ada_Node,
           Name     => Name,
           Def      =>
             New_Universal_Quantif
               (Binders => Binders, Triggers => Triggers, Pred => Ax_Body),
           Dep      => Dep);
   end New_Guarded_Axiom;

   ---------------------------
   -- New_Record_Definition --
   ---------------------------

   function New_Record_Definition
     (Ada_Node : Node_Id := Empty; Name : W_Name_Id; Binders : Binder_Array)
      return W_Declaration_Id is
   begin
      return
        New_Type_Decl
          (Ada_Node   => Ada_Node,
           Name       => Name,
           Labels     => Symbol_Sets.Empty_Set,
           Definition =>
             New_Record_Definition
               (Fields => New_Constant_Record_Binders (Binders)));
   end New_Record_Definition;

   ---------------------------
   -- New_Universal_Quantif --
   ---------------------------

   function New_Universal_Quantif
     (Ada_Node : Node_Id := Empty;
      Binders  : Binder_Array;
      Triggers : W_Triggers_OId := Why_Empty;
      Pred     : W_Pred_Id) return W_Pred_Id is
   begin
      if Binders'Length = 0 then
         return Pred;

      else
         return
           New_Universal_Quantif
             (Ada_Node => Ada_Node,
              Binders  => New_Binders (EW_Pred, Binders),
              Labels   => Symbol_Sets.Empty_Set,
              Triggers => Triggers,
              Pred     => Pred);
      end if;
   end New_Universal_Quantif;

   -------------------------
   -- Object_Has_Valid_Id --
   -------------------------

   function Object_Has_Valid_Id (Obj : Entity_Id) return Boolean is
      C : constant Ada_Ent_To_Why.Cursor :=
        Ada_Ent_To_Why.Find (Symbol_Table, Obj);
   begin
      if Ada_Ent_To_Why.Has_Element (C) then
         return Ada_Ent_To_Why.Element (C).Valid.Present;
      end if;
      return False;
   end Object_Has_Valid_Id;

   ----------------------------------
   -- Push_Binders_To_Symbol_Table --
   ----------------------------------

   procedure Push_Binders_To_Symbol_Table (Binders : Item_Array) is
   begin
      for B of Binders loop
         declare
            Node : constant Node_Id := Get_Ada_Node_From_Item (B);
         begin
            if Present (Node) then
               Ada_Ent_To_Why.Insert (Symbol_Table, Node, B);
            else
               pragma Assert (B.Kind = Regular);
               if B.Main.B_Ent /= Null_Entity_Name then

                  --  If there is no Ada_Node, this is a binder generated from
                  --  an effect; we add the parameter in the name map using its
                  --  unique name.

                  Ada_Ent_To_Why.Insert (Symbol_Table, B.Main.B_Ent, B);
               end if;
            end if;
         end;
      end loop;
   end Push_Binders_To_Symbol_Table;

   ------------------------
   -- Reconstruct_Binder --
   ------------------------

   function Reconstruct_Binder
     (Id          : W_Identifier_Id;
      Mutable     : Boolean;
      Domain      : EW_Domain;
      Ref_Allowed : Boolean := True;
      Alias       : W_Expr_Id := Why_Empty) return W_Expr_Id is
   begin
      if not Mutable then
         return +Id;
      elsif Present (Alias) then
         return
           New_Call
             (Domain => Domain,
              Name   => Id,
              Args   => (1 => Alias),
              Typ    => Get_Typ (Id));
      elsif Ref_Allowed then
         return
           New_Deref
             (Ada_Node => Get_Ada_Node (+Id),
              Right    => Id,
              Typ      => Get_Typ (Id));
      else
         return +Id;
      end if;
   end Reconstruct_Binder;

   ----------------------
   -- Reconstruct_Item --
   ----------------------

   function Reconstruct_Item
     (E           : Item_Type;
      Domain      : EW_Domain;
      Ref_Allowed : Boolean := True;
      Alias       : W_Expr_Id := Why_Empty) return W_Expr_Id
   is
      T : W_Expr_Id;
   begin
      case E.Kind is
         when Subp                      =>
            raise Program_Error;

         when Regular | Concurrent_Self =>
            T :=
              Reconstruct_Binder
                (E.Main.B_Name, E.Main.Mutable, Domain, Ref_Allowed, Alias);

         when UCArray                   =>
            T := Array_From_Split_Form (E, Domain, Ref_Allowed, Alias);

         when DRecord                   =>
            T := Record_From_Split_Form (E, Domain, Ref_Allowed, Alias);

         when Pointer                   =>
            pragma Assert (No (Alias));

            T := +Pointer_From_Split_Form (E, Ref_Allowed);

      end case;

      return T;
   end Reconstruct_Item;

   ---------------------
   -- To_Binder_Array --
   ---------------------

   function To_Binder_Array
     (A : Item_Array; Keep_Const : Handling := Local_Only) return Binder_Array
   is
      function Keep_Local (Is_Local : Boolean) return Boolean
      is (case Keep_Const is
            when Keep       => True,
            when Local_Only => Is_Local,
            when Erase      => False);

      Result : Binder_Array (1 .. Item_Array_Length (A, Keep_Const));
      Count  : Natural := 1;
   begin
      for Index in A'Range loop
         declare
            Cur : Item_Type renames A (Index);
         begin
            if Cur.Init.Present then
               Result (Count) :=
                 (B_Name => Cur.Init.Id, Mutable => True, others => <>);
               Count := Count + 1;
            end if;

            if Cur.Valid.Present then
               Result (Count) :=
                 (B_Name  => Cur.Valid.Id,
                  Mutable => Item_Is_Mutable (Cur),
                  others  => <>);
               Count := Count + 1;
            end if;

            case Cur.Kind is
               when Regular | Concurrent_Self =>
                  if Keep_Local (Cur.Local) or else Cur.Main.Mutable then
                     Result (Count) := Cur.Main;
                     Count := Count + 1;
                  end if;

               when UCArray                   =>
                  Result (Count) := Cur.Content;
                  Count := Count + 1;

                  if Keep_Local (Cur.Local) then
                     for Dim_Index in 1 .. Cur.Dim loop
                        Result (Count) :=
                          (B_Name => Cur.Bounds (Dim_Index).First,
                           others => <>);
                        Result (Count + 1) :=
                          (B_Name => Cur.Bounds (Dim_Index).Last,
                           others => <>);
                        Count := Count + 2;
                     end loop;
                  end if;

               when Pointer                   =>
                  Result (Count) := Cur.Value;
                  Count := Count + 1;

                  if Cur.Mutable or else Keep_Local (Cur.Local) then
                     Result (Count) :=
                       (B_Name  => Cur.Is_Null,
                        Mutable => Cur.Mutable,
                        others  => <>);
                     Count := Count + 1;
                  end if;

               when DRecord                   =>
                  if Cur.Fields.Present
                    and then
                      (Keep_Local (Cur.Local)
                       or else Cur.Fields.Binder.Mutable)
                  then
                     Result (Count) := Cur.Fields.Binder;
                     Count := Count + 1;
                  end if;
                  if Cur.Discrs.Present
                    and then
                      (Keep_Local (Cur.Local)
                       or else Cur.Discrs.Binder.Mutable)
                  then
                     Result (Count) := Cur.Discrs.Binder;
                     Count := Count + 1;
                  end if;
                  if Keep_Local (Cur.Local) and then Cur.Constr.Present then
                     Result (Count) := (B_Name => Cur.Constr.Id, others => <>);
                     Count := Count + 1;
                  end if;
                  if Keep_Local (Cur.Local) and then Cur.Tag.Present then
                     Result (Count) := (B_Name => Cur.Tag.Id, others => <>);
                     Count := Count + 1;
                  end if;

               when Subp                      =>
                  raise Program_Error;
            end case;
         end;
      end loop;
      pragma Assert (Count = Result'Last + 1);
      return Result;
   end To_Binder_Array;

   ----------------
   -- Unit_Param --
   ----------------

   function Unit_Param
     (Prefix : String := ""; Ada_Node : Node_Id := Empty) return Binder_Type is
   begin
      return
        (B_Name   =>
           New_Identifier
             (Name => Prefix & "__void_param", Typ => EW_Unit_Type),
         B_Ent    => Null_Entity_Name,
         Mutable  => False,
         Ada_Node => Ada_Node,
         Labels   => <>);
   end Unit_Param;

end Why.Gen.Binders;
