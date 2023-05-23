------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--               SPARK.CONTAINERS.FUNCTIONAL.SETS.HIGHER_ORDER              --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--          Copyright (C) 2023-2023, Free Software Foundation, Inc.         --
--                                                                          --
-- SPARK is free software;  you can  redistribute it and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion. SPARK is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.                                     --
--                                                                          --
-- As a special exception under Section 7 of GPL version 3, you are granted --
-- additional permissions described in the GCC Runtime Library Exception,   --
-- version 3.1, as published by the Free Software Foundation.               --
--                                                                          --
-- You should have received a copy of the GNU General Public License and    --
-- a copy of the GCC Runtime Library Exception along with this program;     --
-- see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see    --
-- <http://www.gnu.org/licenses/>.                                          --
--                                                                          --
------------------------------------------------------------------------------

pragma Ada_2012;
with SPARK.Big_Integers;  use SPARK.Big_Integers;

package body SPARK.Containers.Functional.Sets.Higher_Order
  with SPARK_Mode =>
#if SPARK_BODY_MODE="On"
  On
#else
  Off
#end if;
is

   -----------------------------------
   -- Local subprogram declarations --
   -----------------------------------

   function All_Distinct
     (New_Length : Big_Natural;
      New_Item   : not null access
        function (I : Big_Positive) return Element_Type)
      return Boolean
   is
     (for all I1 in Interval'(1, New_Length) =>
        (for all I2 in Interval'(1, New_Length) =>
           (if Equivalent_Elements (New_Item (I1), New_Item (I2))
            then I1 = I2)))
   with Ghost;
   --  Check that New_Item always returns distinct elements

   function All_Distinct
     (S              : Set;
      Transform_Item : not null access
        function (I : Element_Type) return Element_Type)
      return Boolean
   is
     (for all E1 of S =>
        (for all E2 of S =>
           (if Equivalent_Elements (Transform_Item (E1), Transform_Item (E2))
            then Equivalent_Elements (E1, E2))))
   with Ghost;
   --  Check that Transform_Item always returns distinct elements

   function Count_Rec
     (S    : Set;
      Test : not null access function (E : Element_Type) return Boolean)
      return Big_Natural
   --  Recursive version of Count

   with
     Subprogram_Variant => (Decreases => Length (S)),
     Post               => Count_Rec'Result <= Length (S);

   procedure Lemma_Count_Rec_Eq
     (S1, S2 : Set;
      Test   : not null access function (E : Element_Type) return Boolean)
   --  Prove Lemma_Count_Eq recursively

   with
     Ghost,
     Pre                => S1 = S2 and then Eq_Compatible (S1, Test),
     Post               => Count_Rec (S1, Test) = Count_Rec (S2, Test),
     Subprogram_Variant => (Decreases => Length (S1), Decreases => 1);

   procedure Lemma_Count_Rec_Remove
     (S    : Set;
      E    : Element_Type;
      Test : not null access function (E : Element_Type) return Boolean)
   --  Prove Lemma_Count_Remove recursively

   with
     Ghost,
     Subprogram_Variant => (Decreases => Length (S), Decreases => 0),
     Pre                => Contains (S, E) and then Eq_Compatible (S, Test),
     Post               =>
       Count_Rec (S, Test) = Count_Rec (Remove (S, E), Test) +
          (if Test (E) then 1 else Big_Natural'(0));

   function Sum_Rec
     (S     : Set;
      Value : not null access function (E : Element_Type) return Big_Integer)
      return Big_Integer
   --  Recursive version of Sum

   with
     Subprogram_Variant => (Decreases => Length (S));

   procedure Lemma_Sum_Rec_Eq
     (S1, S2 : Set;
      Value  : not null access function (E : Element_Type) return Big_Integer)
   --  Prove Lemma_Sum_Eq recursively

   with
     Ghost,
     Pre                => S1 = S2 and then Eq_Compatible (S1, Value),
     Post               => Sum (S1, Value) = Sum (S2, Value),
     Subprogram_Variant => (Decreases => Length (S1), Decreases => 1);

   procedure Lemma_Sum_Rec_Remove
     (S     : Set;
      E     : Element_Type;
      Value : not null access function (E : Element_Type) return Big_Integer)
   --  Prove Lemma_Sum_Remove recursively

   with
     Ghost,
     Subprogram_Variant => (Decreases => Length (S), Decreases => 0),
     Pre                => Contains (S, E) and then Eq_Compatible (S, Value),
     Post               =>
       Sum_Rec (S, Value) = Sum_Rec (Remove (S, E), Value) + Value (E);

   -----------
   -- Count --
   -----------

   function Count
     (S    : Set;
      Test : not null access function (E : Element_Type) return Boolean)
      return Big_Natural
   with Refined_Post => Count'Result = Count_Rec (S, Test)
   is
   begin
      return Res : Big_Natural := 0 do
         for Subset in Iterate (S) loop
            pragma Loop_Invariant
              (Count_Rec (S, Test) = Res + Count_Rec (Subset, Test));
            if Test (Choose (Subset)) then
               Res := Res + 1;
            end if;
         end loop;
      end return;
   end Count;

   ---------------
   -- Count_Rec --
   ---------------

   function Count_Rec
     (S    : Set;
      Test : not null access function (E : Element_Type) return Boolean)
      return Big_Natural
   is
     (if Is_Empty (S) then 0
      else Count_Rec (Remove (S, Choose (S)), Test) +
        (if Test (Choose (S)) then Big_Natural'(1) else 0));

   ------------
   -- Create --
   ------------

   function Create
     (New_Length : Big_Natural;
      New_Item   : not null access
        function (I : Big_Positive) return Element_Type)
      return Set
     with Refined_Post => Length (Create'Result) <= New_Length
       and then
         (if All_Distinct (New_Length, New_Item)
          then Length (Create'Result) = New_Length)
       and then
         (for all I in Interval'(1, New_Length) =>
            Contains (Create'Result, New_Item (I)))
       and then
         (for all E of Create'Result =>
            (for some I in Interval'(1, New_Length) =>
               Equivalent_Elements (E, New_Item (I))))
   is
      I : Big_Natural := 0;
   begin
      return Res : Set do
         while I < New_Length loop
            pragma Loop_Variant (Decreases => New_Length - I);
            pragma Loop_Invariant (I < New_Length);
            pragma Loop_Invariant (Length (Res) <= I);
            pragma Loop_Invariant
              (if All_Distinct (New_Length, New_Item) then Length (Res) = I);
            pragma Loop_Invariant
              (for all J in Interval'(1, I) => Contains (Res, New_Item (J)));
            pragma Loop_Invariant
              (for all E of Res =>
                 (for some J in Interval'(1, I) =>
                      Equivalent_Elements (E, New_Item (J))));
            I := I + 1;
            declare
               E : Element_Type renames New_Item (I);
            begin
               if not Contains (Res, New_Item (I)) then
                  Res := Add (Res, New_Item (I));
               end if;
            end;
         end loop;
      end return;
   end Create;

   ---------------------
   -- Create_Distinct --
   ---------------------

   function Create_Distinct
     (New_Length : Big_Natural;
      New_Item   : not null access
        function (I : Big_Positive) return Element_Type)
      return Set
   is
      I : Big_Positive := 1;
   begin
      return Res : Set do
         while I <= New_Length loop
            Res := Add (Res, New_Item (I));

            pragma Loop_Variant (Decreases => New_Length - I + 1);
            pragma Loop_Invariant (I <= New_Length);
            pragma Loop_Invariant (Length (Res) = I);
            pragma Loop_Invariant
              (for all J in Interval'(1, I) => Contains (Res, New_Item (J)));
            pragma Loop_Invariant
              (for all E of Res =>
                 (for some J in Interval'(1, I) =>
                      Equivalent_Elements (E, New_Item (J))));
            I := I + 1;
         end loop;
      end return;
   end Create_Distinct;

   -------------------
   -- Eq_Compatible --
   -------------------

   function Eq_Compatible
     (S    : Set;
      Test : not null access function (E : Element_Type) return Boolean)
      return Boolean
   is
     (for all E1 of S =>
        (for all E2 of S =>
             (if Equivalent_Elements (E1, E2) then Test (E1) = Test (E2))));

   function Eq_Compatible
     (S     : Set;
      Value : not null access function (E : Element_Type) return Big_Integer)
      return Boolean
   is
     (for all E1 of S =>
        (for all E2 of S =>
             (if Equivalent_Elements (E1, E2)
              then Value (E1) = Value (E2))));

   ------------
   -- Filter --
   ------------

   function Filter
     (S    : Set;
      Test : not null access function (E : Element_Type) return Boolean)
      return Set
   is
   begin
      return Res : Set do
         for Subset in Iterate (S) loop
            pragma Loop_Invariant
              (Length (Res) + Count (Subset, Test) = Count (S, Test));
            pragma Loop_Invariant (Res <= S);
            pragma Loop_Invariant
              (for all E of Res => not Contains (Subset, E));
            pragma Loop_Invariant
              (for all E of S =>
                 (if not Contains (Subset, E) and Test (E)
                  then Contains (Res, E)));
            pragma Loop_Invariant (for all E of Res => Test (E));

            declare
               E : Element_Type renames Choose (Subset);
            begin
               if Test (E) then
                  Res := Add (Res, E);
               end if;
            end;
         end loop;
      end return;
   end Filter;

   ---------------------
   -- Lemma_Count_All --
   ---------------------

   procedure Lemma_Count_All
     (S    : Set;
      Test : not null access function (E : Element_Type) return Boolean)
   is
   begin
      for Subset in Iterate (S) loop
         pragma Loop_Invariant
           (if Count_Rec (Subset, Test) = Length (Subset)
            then Count_Rec (S, Test) = Length (S));
      end loop;
   end Lemma_Count_All;

   --------------------
   -- Lemma_Count_Eq --
   --------------------

   procedure Lemma_Count_Eq
     (S1, S2 : Set;
      Test   : not null access function (E : Element_Type) return Boolean)
   is
   begin
      Lemma_Count_Rec_Eq (S1, S2, Test);
   end Lemma_Count_Eq;

   ----------------------
   -- Lemma_Count_None --
   ----------------------

   procedure Lemma_Count_None
     (S    : Set;
      Test : not null access function (E : Element_Type) return Boolean)
   is
   begin
      for Subset in Iterate (S) loop
         pragma Loop_Invariant
           (if Count_Rec (Subset, Test) = 0 then Count_Rec (S, Test) = 0);
      end loop;
   end Lemma_Count_None;

   ------------------------
   -- Lemma_Count_Rec_Eq --
   ------------------------

   procedure Lemma_Count_Rec_Eq
     (S1, S2 : Set;
      Test   : not null access function (E : Element_Type) return Boolean)
   is
   begin
      if Length (S1) /= 0 then
         declare
            E : constant Element_Type := Choose (S2);
         begin
            Lemma_Count_Rec_Remove (S1, E, Test);
            Lemma_Count_Rec_Eq (Remove (S1, E), Remove (S2, E), Test);
         end;
      end if;
   end Lemma_Count_Rec_Eq;

   ----------------------------
   -- Lemma_Count_Rec_Remove --
   ----------------------------

   procedure Lemma_Count_Rec_Remove
     (S    : Set;
      E    : Element_Type;
      Test : not null access function (E : Element_Type) return Boolean)
   is
      F : constant Element_Type := Choose (S);
   begin
      if not Equivalent_Elements (E, F) then
         Lemma_Count_Rec_Remove (Remove (S, F), E, Test);
         Lemma_Count_Rec_Eq
           (Remove (Remove (S, F), E), Remove (Remove (S, E), F), Test);
         Lemma_Count_Rec_Remove (Remove (S, E), F, Test);
      else
         Lemma_Count_Rec_Eq (Remove (S, F), Remove (S, E), Test);
      end if;
   end Lemma_Count_Rec_Remove;

   ------------------------
   -- Lemma_Count_Remove --
   ------------------------

   procedure Lemma_Count_Remove
     (S    : Set;
      E    : Element_Type;
      Test : not null access function (E : Element_Type) return Boolean)
   is
   begin
      Lemma_Count_Rec_Remove (S, E, Test);
   end Lemma_Count_Remove;

   ---------------------------
   -- Lemma_Create_Distinct --
   ---------------------------

   procedure Lemma_Create_Distinct
     (New_Length : Big_Natural;
      New_Item   : not null access
        function (I : Big_Positive) return Element_Type)
   is null;

   ------------------
   -- Lemma_Sum_Eq --
   ------------------

   procedure Lemma_Sum_Eq
     (S1, S2 : Set;
      Value  : not null access function (E : Element_Type) return Big_Integer)
   is
   begin
      Lemma_Sum_Rec_Eq (S1, S2, Value);
   end Lemma_Sum_Eq;

   ----------------------
   -- Lemma_Sum_Rec_Eq --
   ----------------------

   procedure Lemma_Sum_Rec_Eq
     (S1, S2 : Set;
      Value  : not null access function (E : Element_Type) return Big_Integer)
   is
   begin
      if Length (S1) /= 0 then
         declare
            E : constant Element_Type := Choose (S2);
         begin
            Lemma_Sum_Rec_Remove (S1, E, Value);
            Lemma_Sum_Rec_Eq (Remove (S1, E), Remove (S2, E), Value);
         end;
      end if;
   end Lemma_Sum_Rec_Eq;

   --------------------------
   -- Lemma_Sum_Rec_Remove --
   --------------------------

   procedure Lemma_Sum_Rec_Remove
     (S     : Set;
      E     : Element_Type;
      Value : not null access function (E : Element_Type) return Big_Integer)
   is
      F : constant Element_Type := Choose (S);
   begin
      if not Equivalent_Elements (E, F) then
         Lemma_Sum_Rec_Remove (Remove (S, F), E, Value);
         Lemma_Sum_Rec_Eq
           (Remove (Remove (S, F), E), Remove (Remove (S, E), F), Value);
         Lemma_Sum_Rec_Remove (Remove (S, E), F, Value);
      else
         Lemma_Sum_Rec_Eq (Remove (S, E), Remove (S, F), Value);
      end if;
   end Lemma_Sum_Rec_Remove;

   ----------------------
   -- Lemma_Sum_Remove --
   ----------------------

   procedure Lemma_Sum_Remove
     (S     : Set;
      E     : Element_Type;
      Value : not null access function (E : Element_Type) return Big_Integer)
   is
   begin
      Lemma_Sum_Rec_Remove (S, E, Value);
   end Lemma_Sum_Remove;

   ------------------------------
   -- Lemma_Transform_Distinct --
   ------------------------------

   procedure Lemma_Transform_Distinct
     (S              : Set;
      Transform_Item : not null access
        function (E : Element_Type) return Element_Type)
   is null;

   ---------
   -- Sum --
   ---------

   function Sum
     (S     : Set;
      Value : not null access function (E : Element_Type) return Big_Integer)
      return Big_Integer
   with Refined_Post => Sum'Result = Sum_Rec (S, Value)
   is
   begin
      return Res : Big_Integer := 0 do
         for Subset in Iterate (S) loop
            pragma Loop_Invariant
              (Sum_Rec (S, Value) = Res + Sum_Rec (Subset, Value));
            Res := Res + Value (Choose (Subset));
         end loop;
      end return;
   end Sum;

   -------------
   -- Sum_Rec --
   -------------

   function Sum_Rec
     (S     : Set;
      Value : not null access function (E : Element_Type) return Big_Integer)
      return Big_Integer
   is
     (if Is_Empty (S) then 0
      else Sum_Rec (Remove (S, Choose (S)), Value) + Value (Choose (S)));

   ---------------
   -- Transform --
   ---------------

   function Transform
     (S              : Set;
      Transform_Item : not null access
        function (E : Element_Type) return Element_Type)
      return Set
   with
     Refined_Post => Length (Transform'Result) <= Length (S)
       and then (if All_Distinct (S, Transform_Item)
                 then Length (Transform'Result) = Length (S))
       and then (for all E of S =>
                   Contains (Transform'Result, Transform_Item (E)))
       and then
           (for all E of Transform'Result =>
              (for some F of S =>
                 Equivalent_Elements (E, Transform_Item (F))))
   is
   begin
      return Res : Set do
         for Subset in Iterate (S) loop
            pragma Loop_Invariant
              (Length (Res) + Length (Subset) <= Length (S));
            pragma Loop_Invariant
              (if All_Distinct (S, Transform_Item)
               then Length (Res) + Length (Subset) = Length (S));
            pragma Loop_Invariant
              (for all E of S =>
                 Contains (Subset, E)
                 or else Contains (Res, Transform_Item (E)));
            pragma Loop_Invariant
              (for all E of Res =>
                 (for some F of S => not Contains (Subset, F)
                    and then Equivalent_Elements (E, Transform_Item (F))));

            declare
               E : constant Element_Type := Transform_Item (Choose (Subset));
            begin
               if not Contains (Res, E) then
                  Res := Add (Res, E);
               end if;
            end;
         end loop;
      end return;
   end Transform;

   ------------------------
   -- Transform_Distinct --
   ------------------------

   function Transform_Distinct
     (S              : Set;
      Transform_Item : not null access
        function (E : Element_Type) return Element_Type)
      return Set
   is
   begin
      return Res : Set do
         for Subset in Iterate (S) loop
            pragma Loop_Invariant
              (Length (Res) + Length (Subset) = Length (S));
            pragma Loop_Invariant
              (for all E of S =>
                 Contains (Subset, E)
                 or else Contains (Res, Transform_Item (E)));
            pragma Loop_Invariant
              (for all E of Res =>
                 (for some F of S => not Contains (Subset, F)
                    and then Equivalent_Elements (E, Transform_Item (F))));

            Res := Add (Res, Transform_Item (Choose (Subset)));
         end loop;
      end return;
   end Transform_Distinct;

end SPARK.Containers.Functional.Sets.Higher_Order;
