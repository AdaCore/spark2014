------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--               SPARK.CONTAINERS.FUNCTIONAL.MAPS.HIGHER_ORDER              --
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

package body SPARK.Containers.Functional.Maps.Higher_Order
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

   function Count_Rec
     (M    : Map;
      Test : not null access
        function (K : Key_Type; E : Element_Type) return Boolean)
      return Big_Natural
   --  Recursive version of Count

   with
     Subprogram_Variant => (Decreases => Length (M)),
     Post               => Count_Rec'Result <= Length (M);

   procedure Lemma_Count_Rec_Eq
     (M1, M2 : Map;
      Test   : not null access
        function (K : Key_Type; E : Element_Type) return Boolean)
   --  Prove Lemma_Count_Eq recursively

   with
     Ghost,
     Pre                => Keys_Included (M2, M1)
         and then Elements_Equal (M1, M2) and then Eq_Compatible (M1, Test),
     Post               => Count (M1, Test) = Count (M2, Test),
     Subprogram_Variant => (Decreases => Length (M1), Decreases => 1);

   procedure Lemma_Count_Rec_Remove
     (M    : Maps.Map;
      K    : Key_Type;
      Test : not null access
        function (K : Key_Type; E : Element_Type) return Boolean)
   --  Prove Lemma_Count_Remove recursively

   with
     Ghost,
     Subprogram_Variant => (Decreases => Length (M), Decreases => 0),
     Pre                => Has_Key (M, K) and then Eq_Compatible (M, Test),
     Post               =>
       Count_Rec (M, Test) = Count_Rec (Remove (M, K), Test) +
          (if Test (K, Get (M, K)) then 1 else Big_Natural'(0));

   function Sum_Rec
     (M     : Map;
      Value : not null access
        function (K : Key_Type; E : Element_Type) return Big_Integer)
      return Big_Integer
   --  Recursive version of Sum

   with
     Subprogram_Variant => (Decreases => Length (M));

   procedure Lemma_Sum_Rec_Eq
     (M1, M2 : Map;
      Value  : not null access
        function (K : Key_Type; E : Element_Type) return Big_Integer)
   --  Prove Lemma_Sum_Eq recursively

   with
     Ghost,
     Pre                => Keys_Included (M2, M1)
         and then Elements_Equal (M1, M2) and then Eq_Compatible (M1, Value),
     Post               => Sum (M1, Value) = Sum (M2, Value),
     Subprogram_Variant => (Decreases => Length (M1), Decreases => 1);

   procedure Lemma_Sum_Rec_Remove
     (M     : Maps.Map;
      K     : Key_Type;
      Value : not null access
        function (K : Key_Type; E : Element_Type) return Big_Integer)
   --  Prove Lemma_Sum_Remove recursively

   with
     Ghost,
     Subprogram_Variant => (Decreases => Length (M), Decreases => 0),
     Pre                => Has_Key (M, K) and then Eq_Compatible (M, Value),
     Post               =>
       Sum_Rec (M, Value) =
         Sum_Rec (Remove (M, K), Value) + Value (K, Get (M, K));

   -----------
   -- Count --
   -----------

   function Count
     (M    : Map;
      Test : not null access
        function (K : Key_Type; E : Element_Type) return Boolean)
      return Big_Natural
   with Refined_Post => Count'Result = Count_Rec (M, Test)
   is
   begin
      return Res : Big_Natural := 0 do
         for Submap in Iterate (M) loop
            pragma Loop_Invariant
              (Count_Rec (M, Test) = Res + Count_Rec (Submap, Test));
            declare
               K : Key_Type renames Choose (Submap);
            begin
               if Test (K, Get (Submap, K)) then
                  Res := Res + 1;
               end if;
            end;
         end loop;
      end return;
   end Count;

   ---------------
   -- Count_Rec --
   ---------------

   function Count_Rec
     (M    : Map;
      Test : not null access
        function (K : Key_Type; E : Element_Type) return Boolean)
      return Big_Natural
   is
     (if Is_Empty (M) then 0
      else Count_Rec (Remove (M, Choose (M)), Test) +
        (if Test (Choose (M), Get (M, Choose (M))) then Big_Natural'(1)
         else 0));

   ------------
   -- Create --
   ------------

   function Create
     (New_Length : Big_Natural;
      New_Key    : not null access function (I : Big_Positive) return Key_Type;
      New_Item   : not null access
        function (I : Big_Positive) return Element_Type)
      return Map
   is
      I : Big_Positive := 1;
   begin
      return Res : Map do
         while I <= New_Length loop
            Res := Add (Res, New_Key (I), New_Item (I));
            pragma Loop_Variant (Decreases => New_Length - I + 1);
            pragma Loop_Invariant (I <= New_Length);
            pragma Loop_Invariant (Length (Res) = I);
            pragma Loop_Invariant
              (for all J in Interval'(1, I) => Has_Key (Res, New_Key (J)));
            pragma Loop_Invariant
              (for all K of Res =>
                 (for some J in Interval'(1, I) =>
                      Equivalent_Keys (K, New_Key (J))));
            pragma Loop_Invariant
              (for all J in Interval'(1, I) =>
                   Element_Logic_Equal (Get (Res, New_Key (J)), New_Item (J)));
            I := I + 1;
         end loop;
      end return;
   end Create;

   -------------------
   -- Eq_Compatible --
   -------------------

   function Eq_Compatible
     (M    : Map;
      Test : not null access
        function (K : Key_Type; E : Element_Type) return Boolean)
      return Boolean
   is
     (for all K1 of M =>
        (for all K2 of M =>
             (if Equivalent_Keys (K1, K2)
              then Test (K1, Get (M, K1)) = Test (K2, Get (M, K2)))));

   function Eq_Compatible
     (M     : Map;
      Value : not null access
        function (K : Key_Type; E : Element_Type) return Big_Integer)
      return Boolean
   is
     (for all K1 of M =>
        (for all K2 of M =>
             (if Equivalent_Keys (K1, K2)
              then Value (K1, Get (M, K1)) = Value (K2, Get (M, K2)))));

   ------------
   -- Filter --
   ------------

   function Filter
     (M    : Map;
      Test : not null access
        function (K : Key_Type; E : Element_Type) return Boolean)
      return Map
   is
   begin
      return Res : Map do
         for Submap in Iterate (M) loop
            pragma Loop_Invariant
              (Length (Res) + Count (Submap, Test) = Count (M, Test));
            pragma Loop_Invariant (Elements_Equal (Res, M));
            pragma Loop_Invariant
              (for all K of Res => not Has_Key (Submap, K));
            pragma Loop_Invariant
              (for all K of M =>
                 (if not Has_Key (Submap, K) and Test (K, Get (M, K))
                  then Has_Key (Res, K)));
            pragma Loop_Invariant (for all K of Res => Test (K, Get (M, K)));

            declare
               K : Key_Type renames Choose (Submap);
            begin
               if Test (K, Get (Submap, K)) then
                  Res := Add (Res, K, Get (Submap, K));
               end if;
            end;
         end loop;
      end return;
   end Filter;

   ---------------------
   -- Lemma_Count_All --
   ---------------------

   procedure Lemma_Count_All
     (M    : Map;
      Test : not null access
        function (K : Key_Type; E : Element_Type) return Boolean)
   is
   begin
      for Submap in Iterate (M) loop
         pragma Loop_Invariant
           (if Count_Rec (Submap, Test) = Length (Submap)
            then Count_Rec (M, Test) = Length (M));
      end loop;
   end Lemma_Count_All;

   --------------------
   -- Lemma_Count_Eq --
   --------------------

   procedure Lemma_Count_Eq
     (M1, M2 : Map;
      Test   : not null access
        function (K : Key_Type; E : Element_Type) return Boolean)
   is
   begin
      Lemma_Count_Rec_Eq (M1, M2, Test);
   end Lemma_Count_Eq;

   ----------------------
   -- Lemma_Count_None --
   ----------------------

   procedure Lemma_Count_None
     (M    : Map;
      Test : not null access
        function (K : Key_Type; E : Element_Type) return Boolean)
   is
   begin
      for Submap in Iterate (M) loop
         pragma Loop_Invariant
           (if Count_Rec (Submap, Test) = 0 then Count_Rec (M, Test) = 0);
      end loop;
   end Lemma_Count_None;

   ------------------------
   -- Lemma_Count_Rec_Eq --
   ------------------------

   procedure Lemma_Count_Rec_Eq
     (M1, M2 : Map;
      Test   : not null access
        function (K : Key_Type; E : Element_Type) return Boolean)
   is
   begin
      if Length (M1) /= 0 then
         declare
            K : constant Key_Type := Choose (M2);
         begin
            Lemma_Count_Rec_Remove (M1, K, Test);
            Lemma_Count_Rec_Eq (Remove (M1, K), Remove (M2, K), Test);
         end;
      end if;
   end Lemma_Count_Rec_Eq;

   ----------------------------
   -- Lemma_Count_Rec_Remove --
   ----------------------------

   procedure Lemma_Count_Rec_Remove
     (M    : Maps.Map;
      K    : Key_Type;
      Test : not null access
        function (K : Key_Type; E : Element_Type) return Boolean)
   is
      L : constant Key_Type := Choose (M);
   begin
      if not Equivalent_Keys (L, K) then
         Lemma_Count_Rec_Remove (Remove (M, L), K, Test);
         Lemma_Count_Rec_Eq
           (Remove (Remove (M, L), K), Remove (Remove (M, K), L), Test);
         Lemma_Count_Rec_Remove (Remove (M, K), L, Test);
      else
         Lemma_Count_Rec_Eq (Remove (M, L), Remove (M, K), Test);
      end if;
   end Lemma_Count_Rec_Remove;

   ------------------------
   -- Lemma_Count_Remove --
   ------------------------

   procedure Lemma_Count_Remove
     (M    : Map;
      K    : Key_Type;
      Test : not null access
        function (K : Key_Type; E : Element_Type) return Boolean)
   is
   begin
      Lemma_Count_Rec_Remove (M, K, Test);
   end Lemma_Count_Remove;

   ------------------
   -- Lemma_Sum_Eq --
   ------------------

   procedure Lemma_Sum_Eq
     (M1, M2 : Map;
      Value  : not null access
        function (K : Key_Type; E : Element_Type) return Big_Integer)
   is
   begin
      Lemma_Sum_Rec_Eq (M1, M2, Value);
   end Lemma_Sum_Eq;

   ----------------------
   -- Lemma_Sum_Rec_Eq --
   ----------------------

   procedure Lemma_Sum_Rec_Eq
     (M1, M2 : Map;
      Value  : not null access
        function (K : Key_Type; E : Element_Type) return Big_Integer)
   is
   begin
      if Length (M1) /= 0 then
         declare
            K : constant Key_Type := Choose (M2);
         begin
            Lemma_Sum_Rec_Remove (M1, K, Value);
            Lemma_Sum_Rec_Eq (Remove (M1, K), Remove (M2, K), Value);
         end;
      end if;
   end Lemma_Sum_Rec_Eq;

   --------------------------
   -- Lemma_Sum_Rec_Remove --
   --------------------------

   procedure Lemma_Sum_Rec_Remove
     (M     : Maps.Map;
      K     : Key_Type;
      Value : not null access
        function (K : Key_Type; E : Element_Type) return Big_Integer)
   is
      L : constant Key_Type := Choose (M);
   begin
      if not Equivalent_Keys (L, K) then
         Lemma_Sum_Rec_Remove (Remove (M, L), K, Value);
         Lemma_Sum_Rec_Eq
           (Remove (Remove (M, L), K), Remove (Remove (M, K), L), Value);
         Lemma_Sum_Rec_Remove (Remove (M, K), L, Value);
      else
         Lemma_Sum_Rec_Eq (Remove (M, L), Remove (M, K), Value);
      end if;
   end Lemma_Sum_Rec_Remove;

   ----------------------
   -- Lemma_Sum_Remove --
   ----------------------

   procedure Lemma_Sum_Remove
     (M     : Map;
      K     : Key_Type;
      Value : not null access
        function (K : Key_Type; E : Element_Type) return Big_Integer)
   is
   begin
      Lemma_Sum_Rec_Remove (M, K, Value);
   end Lemma_Sum_Remove;

   ---------
   -- Sum --
   ---------

   function Sum
     (M     : Map;
      Value : not null access
        function (K : Key_Type; E : Element_Type) return Big_Integer)
      return Big_Integer
   with Refined_Post => Sum'Result = Sum_Rec (M, Value)
   is
   begin
      return Res : Big_Integer := 0 do
         for Submap in Iterate (M) loop
            pragma Loop_Invariant
              (Sum_Rec (M, Value) = Res + Sum_Rec (Submap, Value));
            declare
               K : Key_Type renames Choose (Submap);
            begin
               Res := Res + Value (K, Get (Submap, K));
            end;
         end loop;
      end return;
   end Sum;

   -------------
   -- Sum_Rec --
   -------------

   function Sum_Rec
     (M     : Map;
      Value : not null access
        function (K : Key_Type; E : Element_Type) return Big_Integer)
      return Big_Integer
   is
     (if Is_Empty (M) then 0
      else Sum_Rec (Remove (M, Choose (M)), Value) +
          Value (Choose (M), Get (M, Choose (M))));

   ---------------
   -- Transform --
   ---------------

   function Transform
     (M              : Map;
      Transform_Key  : not null access function (K : Key_Type) return Key_Type;
      Transform_Item : not null access
        function (E : Element_Type) return Element_Type)
      return Map
   is
   begin
      return Res : Map do
         for Submap in Iterate (M) loop
            pragma Loop_Invariant
              (Length (Res) + Length (Submap) = Length (M));
            pragma Loop_Invariant
              (for all K of M =>
                 Has_Key (Submap, K) or else Has_Key (Res, Transform_Key (K)));
            pragma Loop_Invariant
              (for all K of Res =>
                 (for some L of M => not Has_Key (Submap, L)
                  and then Equivalent_Keys (K, Transform_Key (L))));
            pragma Loop_Invariant
              (for all K of M =>
                 Has_Key (Submap, K)
               or else Element_Logic_Equal
                 (Get (Res, Transform_Key (K)), Transform_Item (Get (M, K))));

            declare
               K : Key_Type renames Choose (Submap);
            begin
               Res := Add
                 (Res, Transform_Key (K), Transform_Item (Get (Submap, K)));
            end;
         end loop;
      end return;
   end Transform;

   -----------------------
   -- Transform_Element --
   -----------------------

   function Transform_Element
     (M              : Map;
      Transform_Item : not null access
        function (E : Element_Type) return Element_Type)
      return Map
   is
   begin
      return Res : Map do
         for Submap in Iterate (M) loop
            pragma Loop_Invariant
              (Length (Res) + Length (Submap) = Length (M));
            pragma Loop_Invariant
              (for all K of M =>
                 Has_Key (Submap, K) or else Has_Key (Res, K));
            pragma Loop_Invariant
              (for all K of Res =>
                 not Has_Key (Submap, K) and then Has_Key (M, K));
            pragma Loop_Invariant
              (for all K of Res =>
                 Element_Logic_Equal
                   (Get (Res, K), Transform_Item (Get (M, K))));

            declare
               K : Key_Type renames Choose (Submap);
            begin
               Res := Add (Res, K, Transform_Item (Get (Submap, K)));
            end;
         end loop;
      end return;
   end Transform_Element;

end SPARK.Containers.Functional.Maps.Higher_Order;
