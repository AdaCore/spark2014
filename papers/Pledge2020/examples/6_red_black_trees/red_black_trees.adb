package body Red_Black_Trees with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   ------------------------------------------
   -- Local Ghost Subprograms for Ordering --
   ------------------------------------------

   function Is_Concat
     (X1 : Model_Type; I2 : Integer; X3 : Model_Type; I4 : Integer; X5 : Model_Type; R : Model_Type) return Boolean
   is
     (X1'First = R'First and then R'Length - X3'Length > X1'Length
      and then R'Length - X3'Length - X1'Length - 2 = X5'Length
      and then (if X3'Length > 0 then X3'First = X1'First + X1'Length + 1)
      and then (if X5'Length > 0 then X5'First = X1'First + X1'Length + X3'Length + 2)
      and then (for all I in X1'Range => X1 (I) = R (I))
      and then R (X1'First + X1'Length) = I2
      and then (for all I in X3'Range => X3 (I) = R (I))
      and then R (X1'First + X1'Length + X3'Length + 1) = I4
      and then (for all I in X5'Range => X5 (I) = R (I)))
   with Ghost;
   --  Returns True if R is X1 & I2 & X3 & I4 & X4. Used to unfold the tree
   --  twice in a row.

   -------------------------------------------
   -- Local Ghost Subprograms for Balancing --
   -------------------------------------------

   type Structural_Info is record
      Size          : Natural;
      NB_Black      : Natural;
      Same_Nb_Black : Boolean;
      Scarce_Red    : Boolean;
      Root_Color    : Red_Or_Black;
   end record with Ghost;

   function Struct_Info (T : access constant Tree_Cell) return Structural_Info is
     (Size          => Size (T),
      Same_Nb_Black => Same_Nb_Black (T),
      Nb_Black      => Nb_Black (T),
      Scarce_Red    => Scarce_Red (T),
      Root_Color    => Get_Color (T))
   with Ghost,
       Pre => Size (T) < Natural'Last;
   --  Compute information about the form of a tree. Used to express
   --  preservation of the tree's form on rotations.

   ------------
   -- Lemmas --
   ------------

   ------------------------------
   -- About Concatenation Only --
   ------------------------------

   procedure Prove_Concat_Assoc_Right
     (X1 : Model_Type; X2 : Integer; X3 : Model_Type; Y1 : Model_Type; Y2 : Integer; Y3 : Model_Type; R : Model_Type)
   with Ghost,
     Global => null,
     Pre => Is_Concat (X1, X2, X3, R) and then Is_Concat (Y1, Y2, Y3, X3),
     Post => Is_Concat (X1, X2, Y1, Y2, Y3, R);

   procedure Prove_Concat_Assoc_Left
     (X1 : Model_Type; X2 : Integer; X3 : Model_Type; Y1 : Model_Type; Y2 : Integer; Y3 : Model_Type; R : Model_Type)
   with Ghost,
     Global => null,
     Pre => Is_Concat (X1, X2, X3, Y1) and then Is_Concat (Y1, Y2, Y3, R),
     Post => Is_Concat (X1, X2, X3, Y2, Y3, R);

   procedure Prove_Concat_Eq
     (X1 : Model_Type; X2 : Integer; X3 : Model_Type; R1, R2 : Model_Type)
   with Ghost,
     Global => null,
     Pre => Is_Concat (X1, X2, X3, R1) and Is_Concat (X1, X2, X3, R2),
     Post => R1 = R2;

   procedure Prove_Concat_Eq
     (X1 : Model_Type; X2 : Integer; X3 : Model_Type; X4 : Integer; X5 : Model_Type; R1, R2 : Model_Type)
   with Ghost,
     Global => null,
     Pre => Is_Concat (X1, X2, X3, X4, X5, R1) and Is_Concat (X1, X2, X3, X4, X5, R2),
     Post => R1 = R2;

   procedure Prove_Concat_Ext1
     (X1, Y1 : Model_Type; X2 : Integer; X3 : Model_Type; R1, R2 : Model_Type)
   with Ghost,
     Global => null,
     Pre => Is_Concat (X1, X2, X3, R1) and Is_Concat (Y1, X2, X3, R2) and Y1 = X1 and Y1'First = X1'First,
     Post => R1 = R2;

   procedure Prove_Concat_Ext2
     (X1 : Model_Type; X2 : Integer; X3, Y3 : Model_Type; R1, R2 : Model_Type)
   with Ghost,
     Global => null,
     Pre => Is_Concat (X1, X2, X3, R1) and Is_Concat (X1, X2, Y3, R2) and Y3 = X3,
     Post => R1 = R2;

   ---------------------
   -- About Insertion --
   ---------------------

   procedure Prove_Insert_Eq
     (X : Model_Type; V : Integer; R1, R2 : Model_Type)
   with Ghost,
     Global => null,
     Pre => R1 = R2 and Model_Insert (X, V, R1),
     Post => Model_Insert (X, V, R2);

   procedure Prove_Insert_Concat_Left
     (X1, Y1 : Model_Type; X2 : Integer; X3, Y3 : Model_Type; V : Integer; R1, R2 : Model_Type)
   with Ghost,
     Global => null,
     Pre => Is_Concat (X1, X2, X3, R1) and Is_Concat (Y1, X2, Y3, R2) and Model_Insert (X1, V, Y1)
     and (X3'Length = Y3'Length and then (for all I in X3'Range => X3 (I) = Y3 (I - X3'First + Y3'First))),
     Post => Model_Insert (R1, V, R2);

   procedure Prove_Insert_Concat_Right
     (X1 : Model_Type; X2 : Integer; X3, Y3 : Model_Type; V : Integer; R1, R2 : Model_Type)
   with Ghost,
     Global => null,
     Pre => Is_Concat (X1, X2, X3, R1) and Is_Concat (X1, X2, Y3, R2) and Model_Insert (X3, V, Y3),
     Post => Model_Insert (R1, V, R2);

   ---------------------
   -- About Inclusion --
   ---------------------

   procedure Prove_Contains_Concat
     (X1 : Model_Type; X2 : Integer; X3 : Model_Type; R : Model_Type; V : Integer)
   with Ghost,
     Global => null,
     Pre => Is_Concat (X1, X2, X3, R),
     Post => Contains (R, V) = (Contains (X1, V) or X2 = V or Contains (X3, V));

   ----------------------
   -- About Sortedness --
   ----------------------

   procedure Prove_Is_Sorted_Eq (X1 : Model_Type; X2 : Model_Type)
   with Ghost,
     Global => null,
     Pre => X1 = X2 and Is_Sorted (X1),
     Post => Is_Sorted (X2);

   procedure Prove_Is_Sorted_Concat
     (X1 : Model_Type; X2 : Integer; X3 : Model_Type; R : Model_Type)
   with Ghost,
     Global => null,
     Pre => Is_Concat (X1, X2, X3, R)
     and (if X1'Length > 0 then X1 (X1'Last) < X2) and Is_Sorted (X1)
     and (if X3'Length > 0 then X3 (X3'First) > X2) and Is_Sorted (X3),
     Post => Is_Sorted (R);

   procedure Prove_Is_Sorted_Concat_Rev
     (X1 : Model_Type; X2 : Integer; X3 : Model_Type; R : Model_Type)
   with Ghost,
     Global => null,
     Pre => Is_Concat (X1, X2, X3, R) and Is_Sorted (R),
     Post => (if X1'Length > 0 then X1 (X1'Last) < X2) and Is_Sorted (X1)
     and (if X3'Length > 0 then X3 (X3'First) > X2) and Is_Sorted (X3);

   procedure Prove_First_Last_Prop (T1, T2 : Model_Type; V : Integer)
   with Ghost,
     Global => null,
     Pre    => Is_Sorted (T1) and Is_Sorted (T2) and Model_Insert (T1, V, T2),
     Post   =>
       (T2'Length > 0
        and then (if T1'Length = 0 or else T1 (T1'Last) < V then T2 (T2'Last) = V
            else T2 (T2'Last) = T1 (T1'Last))
        and then (if T1'Length = 0 or else T1 (T1'First) > V then T2 (T2'First) = V
            else T2 (T2'First) = T1 (T1'First)));
   --  Gives the values of first and last elements after an insertion in a
   --  sorted array.

   -----------------------------
   -- About Sliding of Models --
   -----------------------------

   procedure Prove_Model_Eq (T : access constant Tree_Cell; Pos1, Pos2 : Positive)
   with Ghost,
     Global => null,
     Pre => Size (T) <= Natural'Last - Pos1 and Size (T) <= Natural'Last - Pos2,
     Post => (Model (T, Pos1)'Length = Model (T, Pos2)'Length
              and then (for all I in Model (T, Pos1)'Range => Model (T, Pos1) (I) = Model (T, Pos2) (I - Pos1 + Pos2))
              and then (for all I in Model (T, Pos2)'Range => Model (T, Pos1) (I - Pos2 + Pos1) = Model (T, Pos2) (I)));

   -------------------------------
   -- Body of Ghost Subprograms --
   -------------------------------

   function Model (X : access constant Tree_Cell; Fst : Positive) return Model_Type is
   begin
      if X = null then
         return (Fst .. Fst - 1 => 0);
      else
         return R : Model_Type := Model (X.Left, Fst) & (Fst => X.Value) &
           Model (X.Right, Fst + Size (X.Left) + 1)
         do
            --  Prove that the result of the concatenation indeed has the
            --  expected properties.

            declare
               X1 : Model_Type := Model (X.Left, Fst);
               X2 : Integer := X.Value;
               X3 : Model_Type := Model (X.Right, Fst + Size (X.Left) + 1);
            begin
               pragma Assert (X1'First = R'First and then X1'Length = R'Length - X3'Length - 1);
               pragma Assert (if X3'Length > 0 then X3'First = X1'First + X1'Length + 1);
               pragma Assert (for all I in X1'Range => X1 (I) = R (I));
               pragma Assert (R (X1'First + X1'Length) = X2);
               pragma Assert (for all I in X3'Range => X3 (I) = R (I));
            end;
         end return;
      end if;
   end Model;

   procedure Prove_Model_Eq (T : access constant Tree_Cell; Pos1, Pos2 : Positive) is
   begin
      --  Proof is done by induction by calling Prove_Model_Eq recursively

      if T /= null then
         Prove_Model_Eq (T.Left, Pos1, Pos2);
         Prove_Model_Eq (T.Right, Pos1 + Size (T.Left) + 1, Pos2 + Size (T.Left) + 1);
         pragma Assert (for all I in Pos1 .. Model (T.Left, Pos1)'Last => Model (T, Pos1) (I) = Model (T, Pos2) (I - Pos1 + Pos2));
         pragma Assert (for all I in Pos1 + Size (T.Left) + 1 .. Model (T.Right, Pos1 + Size (T.Left) + 1)'Last => Model (T, Pos1) (I) = Model (T, Pos2) (I - Pos1 + Pos2));
         pragma Assert (for all I in Model (T, Pos1)'Range => Model (T, Pos1) (I) = Model (T, Pos2) (I - Pos1 + Pos2));
      end if;
   end Prove_Model_Eq;

   procedure Prove_Contains_Concat
     (X1 : Model_Type; X2 : Integer; X3 : Model_Type; R : Model_Type; V : Integer)
   is null;

   procedure Prove_Concat_Assoc_Right
     (X1 : Model_Type; X2 : Integer; X3 : Model_Type; Y1 : Model_Type; Y2 : Integer; Y3 : Model_Type; R : Model_Type)
   is null;

   procedure Prove_Concat_Assoc_Left
     (X1 : Model_Type; X2 : Integer; X3 : Model_Type; Y1 : Model_Type; Y2 : Integer; Y3 : Model_Type; R : Model_Type)
   is null;

   procedure Prove_Concat_Eq
     (X1 : Model_Type; X2 : Integer; X3 : Model_Type; R1, R2 : Model_Type)
   is null;

   procedure Prove_Concat_Eq
     (X1 : Model_Type; X2 : Integer; X3 : Model_Type; X4 : Integer; X5 : Model_Type; R1, R2 : Model_Type)
   is null;

   procedure Prove_Concat_Ext1
     (X1, Y1 : Model_Type; X2 : Integer; X3 : Model_Type; R1, R2 : Model_Type)
   is null;

   procedure Prove_Concat_Ext2
     (X1 : Model_Type; X2 : Integer; X3, Y3 : Model_Type; R1, R2 : Model_Type)
   is null;

   procedure Prove_Insert_Eq
     (X : Model_Type; V : Integer; R1, R2 : Model_Type)
   is null;

   procedure Prove_Insert_Concat_Left
     (X1, Y1 : Model_Type; X2 : Integer; X3, Y3 : Model_Type; V : Integer; R1, R2 : Model_Type)
   is
   begin
      pragma Assert (for all I in Y3'Range => X3 (I - Y3'First + X3'First) = Y3 (I));
   end Prove_Insert_Concat_Left;

   procedure Prove_Insert_Concat_Right
     (X1 : Model_Type; X2 : Integer; X3, Y3 : Model_Type; V : Integer; R1, R2 : Model_Type)
   is null;

   procedure Prove_Is_Sorted_Eq (X1 : Model_Type; X2 : Model_Type)
   is null;

   procedure Prove_Is_Sorted_Concat
     (X1 : Model_Type; X2 : Integer; X3 : Model_Type; R : Model_Type)
   is null;

   procedure Prove_Is_Sorted_Concat_Rev
     (X1 : Model_Type; X2 : Integer; X3 : Model_Type; R : Model_Type)
   is null;

   procedure Prove_First_Last_Prop (T1, T2 : Model_Type; V : Integer) is null;

   -------------------------
   -- Regular Subprograms --
   -------------------------

   function Contains (T : access constant Tree_Cell; V : Integer) return Boolean is
      C   : access constant Tree_Cell := T;
      Pos : Positive := 1 with Ghost;
      --  Ghost variable to hold the position of the first indice of the model
      --  of C in the model of T.

   begin
      while C /= null loop
         pragma Loop_Invariant (Size (C) <= Size (T) - Pos + 1);
         pragma Loop_Invariant (Is_Sorted (Model (C, Pos)));
         pragma Loop_Invariant
           (Contains (Model (T), V) = Contains (Model (C, Pos), V));

         --  Prove that C.Left and C.Right are sorted

         Prove_Is_Sorted_Concat_Rev
           (X1 => Model (C.Left, Pos),
            X2 => C.Value,
            X3 => Model (C.Right, Pos + Size (C.Left) + 1),
            R  => Model (C, Pos));

         --  Case by case analysis for inclusion in C

         Prove_Contains_Concat
           (X1 => Model (C.Left, Pos),
            X2 => C.Value,
            X3 => Model (C.Right, Pos + Size (C.Left) + 1),
            R  => Model (C, Pos),
            V  => V);

         if C.Value = V then
            return True;
         elsif C.Value < V then
            Pos := Pos + Size (C.Left) + 1;
            C := C.Right;
         else
            C := C.Left;
         end if;
      end loop;
      return False;
   end Contains;

   procedure Rotate_Left (T : in out Tree; Pos : Positive) with
     Pre => T /= null and then T.Right /= null and then Size (T) <= Natural'Last - Pos,
     Post =>

     --  Model of T is preserved

       Size (T) = Size (T)'Old
     and Model (T, Pos) = Model (T, Pos)'Old

     --  Additional information over the form of T.
     --  Used for balancing.

     and T.Color = T.Right.Color'Old
     and Struct_Info (T.Right) = Struct_Info (T.Right.Right)'Old
     and T.Left /= null
     and T.Left.Color = T.Color'Old
     and Struct_Info (T.Left.Left) = Struct_Info (T.Left)'Old
     and Struct_Info (T.Left.Right) = Struct_Info (T.Right.Left)'Old
   is
      T_Old : constant Model_Type := Model (T, Pos) with Ghost;
   begin
      --  Deconstruct T to describe its model in term of the models of its
      --  parts.

      Prove_Concat_Assoc_Right
        (Model (T.Left, Pos), T.Value, Model (T.Right, Size (T.Left) + Pos + 1),
         Model (T.Right.Left, Size (T.Left) + Pos + 1), T.Right.Value, Model (T.Right.Right, Size (T.Left) + Pos + 2 + Size (T.Right.Left)),
         Model (T, Pos));

      declare
         Tnew : Tree := T.Right;
      begin
         T.Right := Tnew.Left;
         Tnew.Left := T;
         T := Tnew;
      end;

      --  Deconstruct T to describe its model in term of the models of its
      --  parts.

      Prove_Concat_Assoc_Left
        (Model (T.Left.Left, Pos) , T.Left.Value, Model (T.Left.Right, Size (T.Left.Left) + Pos + 1),
         Model (T.Left, Pos), T.Value, Model (T.Right, Size (T.Left) + Pos + 1),
         Model (T, Pos));

      --  Model (T, Pos) and T_Old are the same since they are the concatenation
      --  of the same parts.

      Prove_Concat_Eq
        (Model (T.Left.Left, Pos) , T.Left.Value, Model (T.Left.Right, Size (T.Left.Left) + Pos + 1),
         T.Value, Model (T.Right, Size (T.Left) + Pos + 1),
         Model (T, Pos), T_Old);
   end Rotate_Left;

   procedure Rotate_Right (T : in out Tree; Pos : Positive) with
     Pre => T /= null and then T.Left /= null and then Size (T) <= Natural'Last - Pos,
     Post =>

     --  Model of T is preserved

       Size (T) = Size (T)'Old
     and Model (T, Pos) = Model (T, Pos)'Old

     --  Additional information over the form of T.
     --  Used for balancing.

     and T.Color = T.Left.Color'Old
     and Struct_Info (T.Left) = Struct_Info (T.Left.Left)'Old
     and T.Right /= null
     and T.Right.Color = T.Color'Old
     and Struct_Info (T.Right.Left) = Struct_Info (T.Left.Right)'Old
     and Struct_Info (T.Right.Right) = Struct_Info (T.Right)'Old
   is
      T_Old : constant Model_Type := Model (T, Pos) with Ghost;
   begin
      --  Deconstruct T to describe its model in term of the models of its
      --  parts.

      Prove_Concat_Assoc_Left
        (Model (T.Left.Left, Pos) , T.Left.Value, Model (T.Left.Right, Size (T.Left.Left) + Pos + 1),
         Model (T.Left, Pos), T.Value, Model (T.Right, Size (T.Left) + Pos + 1),
         Model (T, Pos));

      declare
         Tnew : Tree := T.Left;
      begin
         T.Left := Tnew.Right;
         Tnew.Right := T;
         T := Tnew;
      end;

      --  Deconstruct T to describe its model in term of the models of its
      --  parts.

      Prove_Concat_Assoc_Right
        (Model (T.Left, Pos), T.Value, Model (T.Right, Size (T.Left) + Pos + 1),
         Model (T.Right.Left, Size (T.Left) + Pos + 1), T.Right.Value, Model (T.Right.Right, Size (T.Left) + Pos + 2 + Size (T.Right.Left)),
         Model (T, Pos));

      --  Model (T, Pos) and T_Old are the same since they are the concatenation
      --  of the same parts.

      Prove_Concat_Eq
        (Model (T.Left, Pos), T.Value,
         Model (T.Right.Left, Size (T.Left) + Pos + 1), T.Right.Value, Model (T.Right.Right, Size (T.Left) + Pos + 2 + Size (T.Right.Left)),
         Model (T, Pos), T_Old);
   end Rotate_Right;

   procedure Balance (T : in out Tree; Pos : Positive) with
     Pre => T /= null and then Size (T) <= Natural'Last - Pos

     --  Insertion as preserved the number of black node in every branch

     and then Same_Nb_Black (T)

     --  But a red node may have been inserting, possibly breaking scarcity
     --  of red:

     and then

     --   * at the top-level if T is labelled red

       (if T.Color = Red then Scarce_Red (T.Left) and Scarce_Red (T.Right)

     --   * at the top-level in the left *or* the right subtree if T is
     --     labelled black.

        else ((Scarce_Red (T.Left)
               and then T.Right /= null
               and then Scarce_Red (T.Right.Left)
               and then Scarce_Red (T.Right.Right))
              or (Scarce_Red (T.Right)
                  and then T.Left /= null
                  and then Scarce_Red (T.Left.Right)
                  and then Scarce_Red (T.Left.Left)))),
     Post =>

     --  Balancing does not modify the model of the tree

       Size (T) = Size (T)'Old
     and Model (T, Pos) = Model (T, Pos)'Old

     --  It does not modify the number of black nodes in branches either

     and Same_Nb_Black (T)
     and Nb_Black (T) = Nb_Black (T)'Old

     --  But if T was labelled black, it will have been rebalanced

     and (if Get_Color (T)'Old = Black then Scarce_Red (T)
          else Scarce_Red (T.Left) and Scarce_Red (T.Right))
   is
      Nb_Black_Old : constant Natural := Nb_Black (T) with Ghost;
      T_Old        : constant Model_Type := Model (T, Pos) with Ghost;
   begin
      if T.Color = Black
        and then T.Left /= null
        and then T.Left.Color = Red
      then
         if T.Left.Left /= null
           and then T.Left.Left.Color = Red
         then
            Rotate_Right (T, Pos);

            declare
               TL_Old : constant Model_Type := Model (T.Left, Pos) with Ghost;
               T2_Old : constant Model_Type := Model (T, Pos) with Ghost;
            begin
               T.Left.Color := Black;

               --  Prove that we have not modified the model

               Prove_Concat_Eq (Model (T.Left.Left, Pos), T.Left.Value, Model (T.Left.Right, Pos + 1 + Size (T.Left.Left)), TL_Old, Model (T.Left, Pos));
               Prove_Concat_Ext1 (TL_Old, Model (T.Left, Pos), T.Value, Model (T.Right, Pos + 1 + Size (T.Left)), T2_Old, Model (T, Pos));
            end;

            --  Restate the postcondition to facilitate verification

            pragma Assert (Model (T, Pos) = T_Old);
            pragma Assert (Scarce_Red (T));
            pragma Assert (Same_Nb_Black (T));
            pragma Assert (Nb_Black (T) = Nb_Black_Old);

         elsif T.Left.Right /= null
           and then T.Left.Right.Color = Red
         then
            declare
               TL_Old : constant Model_Type := Model (T.Left, Pos) with Ghost;
            begin
               Rotate_Left (T.Left, Pos);

               --  Prove that we have not modified the model

               Prove_Concat_Ext1 (TL_Old, Model (T.Left, Pos), T.Value, Model (T.Right, Pos + 1 + Size (T.Left)), T_Old, Model (T, Pos));
            end;

            Rotate_Right (T, Pos);

            declare
               T2_Old : constant Model_Type := Model (T, Pos) with Ghost;
               TL_Old : constant Model_Type := Model (T.Left, Pos) with Ghost;
            begin
               T.Left.Color := Black;

               --  Prove that we have not modified the model

               Prove_Concat_Eq (Model (T.Left.Left, Pos), T.Left.Value, Model (T.Left.Right, Pos + 1 + Size (T.Left.Left)), TL_Old, Model (T.Left, Pos));
               Prove_Concat_Ext1 (TL_Old, Model (T.Left, Pos), T.Value, Model (T.Right, Pos + 1 + Size (T.Left)), T2_Old, Model (T, Pos));
            end;

            --  Restate the postcondition to facilitate verification

            pragma Assert (Model (T, Pos) = T_Old);
            pragma Assert (Scarce_Red (T));
            pragma Assert (Same_Nb_Black (T));
            pragma Assert (Nb_Black (T) = Nb_Black_Old);
         end if;
      end if;
      if T.Color = Black
        and then T.Right /= null
        and then T.Right.Color = Red
      then
         if T.Right.Right /= null
           and then T.Right.Right.Color = Red
         then
            Rotate_Left (T, Pos);

            declare
               T2_Old : constant Model_Type := Model (T, Pos) with Ghost;
               TR_Old : constant Model_Type := Model (T.Right, Pos + Size (T.Left) + 1) with Ghost;
            begin
               T.Right.Color := Black;

               --  Prove that we have not modified the model

               Prove_Concat_Eq (Model (T.Right.Left, Pos + Size (T.Left) + 1), T.Right.Value, Model (T.Right.Right, Pos + 2 + Size (T.Left) + Size (T.Right.Left)), TR_Old, Model (T.Right, Pos + Size (T.Left) + 1));
               Prove_Concat_Ext2 (Model (T.Left, Pos), T.Value, TR_Old, Model (T.Right, Pos + 1 + Size (T.Left)), T2_Old, Model (T, Pos));
            end;

            --  Restate the postcondition to facilitate verification

            pragma Assert (Model (T, Pos) = T_Old);
            pragma Assert (Scarce_Red (T));
            pragma Assert (Same_Nb_Black (T));
            pragma Assert (Nb_Black (T) = Nb_Black_Old);

         elsif T.Right.Left /= null
           and then T.Right.Left.Color = Red
         then
            declare
               TR_Old : constant Model_Type := Model (T.Right, Pos + Size (T.Left) + 1) with Ghost;
            begin
               Rotate_Right (T.Right, Pos + Size (T.Left) + 1);

               --  Prove that we have not modified the model

               Prove_Concat_Ext2 (Model (T.Left, Pos), T.Value, TR_Old, Model (T.Right, Pos + 1 + Size (T.Left)), T_Old, Model (T, Pos));
            end;

            Rotate_Left (T, Pos);

            declare
               T2_Old : constant Model_Type := Model (T, Pos) with Ghost;
               TR_Old : constant Model_Type := Model (T.Right, Pos + Size (T.Left) + 1) with Ghost;
            begin
               T.Right.Color := Black;

               --  Prove that we have not modified the model

               Prove_Concat_Eq (Model (T.Right.Left, Pos + Size (T.Left) + 1), T.Right.Value, Model (T.Right.Right, Pos + 2 + Size (T.Left) + Size (T.Right.Left)), TR_Old, Model (T.Right, Pos + Size (T.Left) + 1));
               Prove_Concat_Ext2 (Model (T.Left, Pos), T.Value, TR_Old, Model (T.Right, Pos + 1 + Size (T.Left)), T2_Old, Model (T, Pos));
            end;

            --  Restate the postcondition to facilitate verification

            pragma Assert (Model (T, Pos) = T_Old);
            pragma Assert (Scarce_Red (T));
            pragma Assert (Same_Nb_Black (T));
            pragma Assert (Nb_Black (T) = Nb_Black_Old);
         end if;
      end if;
   end Balance;

   procedure Insert_Rec (T : in out Tree; V : Integer; Pos : Positive) with
     Pre  => Size (T) < Natural'Last - Pos

     --  Invariants of red black trees without the part about the root

     and then Is_Sorted (Model (T, Pos))
     and then Scarce_Red (T)
     and then Same_Nb_Black (T),

     Post =>

     --  V has been inserted in the model of T

       T /= null and Size (T) in Size (T)'Old .. Size (T)'Old + 1
     and Model_Insert (Model (T, Pos)'Old, V, Model (T, Pos))

     --  Partial reestablishment of red black trees' invariants:
     --   * T is sorted

     and Is_Sorted (Model (T, Pos))

     --   * The number of black nodes on every branches was preserved

     and Same_Nb_Black (T)
     and Nb_Black (T) = Nb_Black (T)'Old

     --   * If the root node of T was black, the scarcity of red has been
     --     reestablished. Otherwise, it may be broken at the root of T.

     and (if Get_Color (T)'Old = Black then Scarce_Red (T)
          else Scarce_Red (T.Left) and Scarce_Red (T.Right))
   is
      T_Old : constant Model_Type := Model (T, Pos) with Ghost;
   begin
      if T = null then
         T := new Tree_Cell'(Value => V,
                             Color => Red,
                             Left  => null,
                             Right => null);
      elsif T.Value = V then

         --  Restate the postcondition to facilitate verification

         pragma Assert (Model_Insert (T_Old, V, Model (T, Pos)));
         pragma Assert (Is_Sorted (Model (T, Pos)));
         return;

      elsif T.Value > V then
         declare
            TL_Old : constant Model_Type := Model (T.Left, Pos) with Ghost;

         begin
            --  T.Left is sorted

            Prove_Is_Sorted_Concat_Rev
              (Model (T.Left, Pos), T.Value, Model (T.Right, Pos + TL_Old'Length + 1), Model (T, Pos));

            Insert_Rec (T.Left, V, Pos);

            --  The model of T.Right has been slided to the left

            Prove_Model_Eq (T.Right, Pos + TL_Old'Length + 1, Pos + Size (T.Left) + 1);

            --  T is still sorted

            Prove_First_Last_Prop (TL_Old, Model (T.Left, Pos), V);
            Prove_Is_Sorted_Concat (Model (T.Left, Pos), T.Value, Model (T.Right, Pos + Size (T.Left) + 1), Model (T, Pos));

            --  V has been inserted in the model of T

            Prove_Insert_Concat_Left
              (TL_Old, Model (T.Left, Pos), T.Value,
               Model (T.Right, Pos + TL_Old'Length + 1), Model (T.Right, Pos + Size (T.Left) + 1),
               V, T_Old, Model (T, Pos));
         end;
      else
         pragma Assert (T.Value < V);

         declare
            TR_Old : constant Model_Type := Model (T.Right, Pos + Size (T.Left) + 1) with Ghost;

         begin
            --  T.Right is sorted

            Prove_Is_Sorted_Concat_Rev (Model (T.Left, Pos), T.Value, Model (T.Right, Pos + Size (T.Left) + 1), Model (T, Pos));

            Insert_Rec (T.Right, V, Pos + Size (T.Left) + 1);

            --  T is still sorted

            Prove_First_Last_Prop (TR_Old, Model (T.Right, Pos + Size (T.Left) + 1), V);
            Prove_Is_Sorted_Concat (Model (T.Left, Pos), T.Value, Model (T.Right, Pos + Size (T.Left) + 1), Model (T, Pos));

            --  V has been inserted in the model of T

            Prove_Insert_Concat_Right
              (Model (T.Left, Pos), T.Value,
               TR_Old, Model (T.Right, Pos + Size (T.Left) + 1),
               V, T_Old, Model (T, Pos));
         end;
      end if;
      pragma Assert (Model_Insert (T_Old, V, Model (T, Pos)));

      declare
         T_Interm : constant Model_Type := Model (T, Pos) with Ghost;
      begin
         Balance (T, Pos);

         --  Since the model of T has not been modified, it is still sorted
         --  and V has been inserted in it.

         Prove_Insert_Eq (T_Old, V, T_Interm, Model (T, Pos));
         Prove_Is_Sorted_Eq (T_Interm, Model (T, Pos));
      end;
   end Insert_Rec;

   procedure Insert (T : in out Tree; V : Integer) is
      T_Old : constant Model_Type := Model (T) with Ghost;
   begin
      Insert_Rec (T, V, 1);

      declare
         T2_Old : constant Model_Type := Model (T) with Ghost;
      begin
         T.Color := Black;

         --  Prove that the model of T is preserved

         Prove_Concat_Eq (Model (T.Left), T.Value, Model (T.Right, 2 + Size (T.Left)), T2_Old, Model (T));
      end;

      --  Restate the postcondition to facilitate verification

      pragma Assert (Balanced (T));
      pragma Assert (Is_Sorted (Model (T)));
   end Insert;

end Red_Black_Trees;
