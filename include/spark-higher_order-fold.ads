------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--              S P A R K . H I G H E R _ O R D E R . F O L D               --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2018-2020, AdaCore                     --
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

package SPARK.Higher_Order.Fold with SPARK_Mode is

   generic
      type Index_Type is range <>;
      type Element_In is private;
      type Array_Type is array (Index_Type range <>) of Element_In;
      type Element_Out is private;
      with function Ind_Prop
        (A : Array_Type;
         X : Element_Out;
         I : Index_Type) return Boolean;
      --  Potential inductive property that should be maintained during fold

      with function Final_Prop
        (A : Array_Type;
         X : Element_Out) return Boolean;
      --  Potential inductive property at the last iteration

      with function F (X : Element_In; I : Element_Out) return Element_Out;
      --  Function that should be applied to elements of Array_Type

   package Fold_Left_Acc is
      pragma Annotate (GNATprove, Terminating, Fold_Left_Acc);

      procedure Prove_Ind (A : Array_Type; X : Element_Out; I : Index_Type)
      with
        Ghost,
        Pre  => I in A'Range and then Ind_Prop (A, X, I) and then I /= A'Last,
        Post => Ind_Prop (A, F (A (I), X), I + 1);
      --  Axiom: Ind_Prop should be preserved when going to next index

      procedure Prove_Last (A : Array_Type; X : Element_Out) with
        Ghost,
        Pre  => A'Length > 0 and then Ind_Prop (A, X, A'Last),
        Post => Final_Prop (A, F (A (A'Last), X));
      --  Axiom: Final_Prop should be provable at the last iteration from
      --  Ind_Prop.

      type Acc_Array is array (Index_Type range <>) of Element_Out;

      function Fold (A : Array_Type; Init : Element_Out) return Acc_Array with
        Pre  => A'Length > 0 and then Ind_Prop (A, Init, A'First),
        Post => Fold'Result'First = A'First
        and then Fold'Result'Last = A'Last
        and then Ind_Prop (A, Init, A'First)
        and then Fold'Result (A'First) = F (A (A'First), Init)
        and then (for all I in A'Range =>
                    (if I > A'First then Ind_Prop (A, Fold'Result (I - 1), I)
                     and then Fold'Result (I) =
                         F (A (I), Fold'Result (I - 1))))
        and then Final_Prop (A, Fold'Result (A'Last));
   end Fold_Left_Acc;

   generic
      type Index_Type is range <>;
      type Element_In is private;
      type Array_Type is array (Index_Type range <>) of Element_In;
      type Element_Out is private;
      with function Ind_Prop
        (A : Array_Type;
         X : Element_Out;
         I : Index_Type) return Boolean;
      --  Potential inductive property that should be maintained during fold

      with function Final_Prop
        (A : Array_Type;
         X : Element_Out) return Boolean;
      --  Potential inductive property at the last iteration

      with function F (X : Element_In; I : Element_Out) return Element_Out;
      --  Function that should be applied to elements of Array_Type

   package Fold_Left is
      pragma Annotate (GNATprove, Terminating, Fold_Left);

      package Acc is new Fold_Left_Acc
        (Index_Type  => Index_Type,
         Element_In  => Element_In,
         Array_Type  => Array_Type,
         Element_Out => Element_Out,
         Ind_Prop    => Ind_Prop,
         Final_Prop  => Final_Prop,
         F           => F);

      function Fold (A : Array_Type; Init : Element_Out) return Element_Out
      with
        Pre  => A'Length = 0 or else Ind_Prop (A, Init, A'First),
        Post => Fold'Result =
          (if A'Length = 0 then Init
           else Acc.Fold (A, Init) (A'Last));
   end Fold_Left;

   generic
      type Index_Type is range <>;
      type Element_In is private;
      type Array_Type is array (Index_Type range <>) of Element_In;
      type Element_Out is private;
      with function Ind_Prop
        (A : Array_Type;
         X : Element_Out;
         I : Index_Type) return Boolean;
      --  Potential inductive property that should be maintained during fold

      with function Final_Prop
        (A : Array_Type;
         X : Element_Out) return Boolean;
      --  Potential inductive property at the last iteration

      with function F
        (X : Element_In;
         K : Index_Type;
         I : Element_Out) return Element_Out;
      --  Function that should be applied to elements of Array_Type

   package Fold_Left_I_Acc is
      pragma Annotate (GNATprove, Terminating, Fold_Left_I_Acc);

      procedure Prove_Ind (A : Array_Type; X : Element_Out; I : Index_Type)
      with
        Ghost,
        Pre  => I in A'Range and then Ind_Prop (A, X, I) and then I /= A'Last,
        Post => Ind_Prop (A, F (A (I), I, X), I + 1);
      --  Axiom: Ind_Prop should be preserved when going to next index

      procedure Prove_Last (A : Array_Type; X : Element_Out) with
        Ghost,
        Pre  => A'Length > 0 and then Ind_Prop (A, X, A'Last),
        Post => Final_Prop (A, F (A (A'Last), A'Last, X));
      --  Axiom: Final_Prop should be provable at the last iteration from
      --  Ind_Prop.

      type Acc_Array is array (Index_Type range <>) of Element_Out;

      function Fold (A : Array_Type; Init : Element_Out) return Acc_Array with
        Pre  => A'Length > 0 and then Ind_Prop (A, Init, A'First),
        Post => Fold'Result'First = A'First
        and then Fold'Result'Last = A'Last
        and then Ind_Prop (A, Init, A'First)
        and then Fold'Result (A'First) = F (A (A'First), A'First, Init)
        and then (for all I in A'Range =>
                    (if I > A'First then Ind_Prop (A, Fold'Result (I - 1), I)
                     and then Fold'Result (I) =
                         F (A (I), I, Fold'Result (I - 1))))
        and then Final_Prop (A, Fold'Result (A'Last));
   end Fold_Left_I_Acc;

   generic
      type Index_Type is range <>;
      type Element_In is private;
      type Array_Type is array (Index_Type range <>) of Element_In;
      type Element_Out is private;
      with function Ind_Prop
        (A : Array_Type;
         X : Element_Out;
         I : Index_Type) return Boolean;
      --  Potential inductive property that should be maintained during fold

      with function Final_Prop
        (A : Array_Type;
         X : Element_Out) return Boolean;
      --  Potential inductive property at the last iteration

      with function F
        (X : Element_In;
         K : Index_Type;
         I : Element_Out) return Element_Out;
      --  Function that should be applied to elements of Array_Type

   package Fold_Left_I is
      pragma Annotate (GNATprove, Terminating, Fold_Left_I);

      package Acc is new Fold_Left_I_Acc
        (Index_Type  => Index_Type,
         Element_In  => Element_In,
         Array_Type  => Array_Type,
         Element_Out => Element_Out,
         Ind_Prop    => Ind_Prop,
         Final_Prop  => Final_Prop,
         F           => F);

      function Fold (A : Array_Type; Init : Element_Out) return Element_Out
      with
        Pre  => A'Length = 0 or else Ind_Prop (A, Init, A'First),
        Post => Fold'Result =
          (if A'Length = 0 then Init
           else Acc.Fold (A, Init) (A'Last));
   end Fold_Left_I;

   generic
      type Index_Type is range <>;
      type Element_In is private;
      type Array_Type is array (Index_Type range <>) of Element_In;
      type Element_Out is private;
      with function Ind_Prop
        (A : Array_Type;
         X : Element_Out;
         I : Index_Type) return Boolean;
      --  Potential inductive property that should be maintained during fold

      with function Final_Prop
        (A : Array_Type;
         X : Element_Out) return Boolean;
      --  Potential inductive property at the last iteration

      with function F (X : Element_In; I : Element_Out) return Element_Out;
      --  Function that should be applied to elements of Array_Type

   package Fold_Right_Acc is
      pragma Annotate (GNATprove, Terminating, Fold_Right_Acc);

      procedure Prove_Ind (A : Array_Type; X : Element_Out; I : Index_Type)
      with
        Ghost,
        Pre  => I in A'Range and then I /= A'First and then Ind_Prop (A, X, I),
        Post => Ind_Prop (A, F (A (I), X), I - 1);
      --  Axiom: Ind_Prop should be preserved when going to previous index

      procedure Prove_Last (A : Array_Type; X : Element_Out) with
        Ghost,
        Pre  => A'Length > 0 and then Ind_Prop (A, X, A'First),
        Post => Final_Prop (A, F (A (A'First), X));
      --  Axiom: Final_Prop should be provable at the last iteration from
      --  Ind_Prop.

      type Acc_Array is array (Index_Type range <>) of Element_Out;

      function Fold (A : Array_Type; Init : Element_Out) return Acc_Array with
        Pre  => A'Length > 0 and then Ind_Prop (A, Init, A'Last),
        Post => Fold'Result'First = A'First
        and then Fold'Result'Last = A'Last
        and then Ind_Prop (A, Init, A'Last)
        and then Fold'Result (A'Last) = F (A (A'Last), Init)
        and then (for all I in A'Range =>
                    (if I < A'Last then Ind_Prop (A, Fold'Result (I + 1), I)
                     and then Fold'Result (I) =
                         F (A (I), Fold'Result (I + 1))))
        and then Final_Prop (A, Fold'Result (A'First));
   end Fold_Right_Acc;

   generic
      type Index_Type is range <>;
      type Element_In is private;
      type Array_Type is array (Index_Type range <>) of Element_In;
      type Element_Out is private;
      with function Ind_Prop
        (A : Array_Type;
         X : Element_Out;
         I : Index_Type) return Boolean;
      --  Potential inductive property that should be maintained during fold

      with function Final_Prop
        (A : Array_Type;
         X : Element_Out) return Boolean;
      --  Potential inductive property at the last iteration

      with function F (X : Element_In; I : Element_Out) return Element_Out;
      --  Function that should be applied to elements of Array_Type

   package Fold_Right is
      pragma Annotate (GNATprove, Terminating, Fold_Right);

      package Acc is new Fold_Right_Acc
        (Index_Type  => Index_Type,
         Element_In  => Element_In,
         Array_Type  => Array_Type,
         Element_Out => Element_Out,
         Ind_Prop    => Ind_Prop,
         Final_Prop  => Final_Prop,
         F           => F);

      function Fold (A : Array_Type; Init : Element_Out) return Element_Out
      with
        Pre  => A'Length = 0 or else Ind_Prop (A, Init, A'Last),
        Post => Fold'Result =
          (if A'Length = 0 then Init
           else Acc.Fold (A, Init) (A'First));
   end Fold_Right;

   generic
      type Index_Type is range <>;
      type Element_In is private;
      type Array_Type is array (Index_Type range <>) of Element_In;
      type Element_Out is range <>;

      with function Value (X : Element_In) return Element_Out;
      --  Sum the value of each element
   package Sum is
      pragma Annotate (GNATprove, Terminating, Sum);

      function In_Range
        (A : Array_Type; X : Element_Out'Base; I : Index_Type) return Boolean
      is (X in Element_Out'First * Element_Out'Base (I - A'First) ..
            Element_Out'Last * Element_Out'Base (I - A'First))
      with Ghost,
        Pre => I in A'Range;

      function In_Range_Last
        (A : Array_Type; X : Element_Out'Base) return Boolean
      is (X in Element_Out'First * A'Length ..
            Element_Out'Last * A'Length)
      with Ghost;

      function Add_Value (X : Element_In; Y : Element_Out'Base) return
        Element_Out'Base
      is (Value (X) + Y)
      with Pre => Y in
          Element_Out'Base'First - Element_Out'Min (0, Element_Out'First) ..
        Element_Out'Base'Last - Element_Out'Max (0, Element_Out'Last);
      pragma Annotate (GNATprove, Inline_For_Proof, Add_Value);

      package Sum_Left is new Fold_Left
        (Index_Type  => Index_Type,
         Element_In  => Element_In,
         Array_Type  => Array_Type,
         Element_Out => Element_Out'Base,
         Ind_Prop    => In_Range,
         Final_Prop  => In_Range_Last,
         F           => Add_Value);

      function Sum (A : Array_Type) return Element_Out'Base is
        (Sum_Left.Fold (A, 0));

      procedure Update_Sum (A1, A2 : Array_Type; I : Index_Type)
      with Ghost,
        Pre  => I in A1'Range and then
        A1'First = A2'First and then A1'Last = A2'Last and then
        (for all K in A1'Range => (if K /= I then A1 (K) = A2 (K))),
        Post => Sum (A2) - Value (A2 (I)) = Sum (A1) - Value (A1 (I));
      --  Lemma: Modification of Sum after an update to the array

      procedure Sum_Cst (A : Array_Type; C : Element_Out) with Ghost,
        Post => (if (for all I in A'Range => Value (A (I)) = C) then
                     Sum (A) = C * A'Length);
      --  Lemma: Value of Sum on a constant array
   end Sum;

   generic
      type Index_Type is range <>;
      type Element is private;
      type Array_Type is array (Index_Type range <>) of Element;
      with function Choose (X : Element) return Boolean;
      --  Count the number of elements for which Choose return True

   package Count is
      pragma Annotate (GNATprove, Terminating, Count);

      function In_Range
        (A : Array_Type; X : Natural; I : Index_Type) return Boolean
      is (X <= Natural (I - A'First))
      with Ghost,
        Pre => I in A'Range;

      function In_Range_Last
        (A : Array_Type; X : Natural) return Boolean
      is (X <= A'Length)
      with Ghost;

      function Add_One (E : Element; X : Natural) return Natural
      is (if Choose (E) then X + 1 else X)
      with Pre => X < Integer'Last;
      pragma Annotate (GNATprove, Inline_For_Proof, Add_One);

      package Count_Left is new Fold_Left
        (Index_Type  => Index_Type,
         Element_In  => Element,
         Array_Type  => Array_Type,
         Element_Out => Natural,
         Ind_Prop    => In_Range,
         Final_Prop  => In_Range_Last,
         F           => Add_One);

      function Count (A : Array_Type) return Natural is
        (Count_Left.Fold (A, 0));

      procedure Update_Count (A1, A2 : Array_Type; I : Index_Type)
      with Ghost,
        Pre => I in A1'Range and then
        A1'First = A2'First and then A1'Last = A2'Last and then
        (for all K in A1'Range => (if K /= I then A1 (K) = A2 (K))),
        Contract_Cases =>
          (Choose (A1 (I)) = Choose (A2 (I))
           =>
             Count (A1) = Count (A2),
           Choose (A1 (I)) and not Choose (A2 (I))
           =>
             Count (A1) = Count (A2) + 1,
           not Choose (A1 (I)) and Choose (A2 (I))
           =>
             Count (A1) + 1 = Count (A2));
      --  Lemma: Modification of Count after an update to the array

      procedure Count_Zero (A : Array_Type) with Ghost,
        Post => (Count (A) = 0) =
          (for all I in A'Range => not Choose (A (I)));
      --  Lemma: Count returns 0 if and only if no element is chosen
   end Count;

   generic
      type Index_1 is range <>;
      type Index_2 is range <>;
      type Element_In is private;
      type Array_Type is array (Index_1 range <>, Index_2 range <>)
        of Element_In;
      type Element_Out is private;
      with function Ind_Prop
        (A : Array_Type;
         X : Element_Out;
         I : Index_1;
         J : Index_2) return Boolean;
      --  Potential inductive property that should be maintained during fold

      with function Final_Prop
        (A : Array_Type;
         X : Element_Out) return Boolean;
      --  Potential inductive property at the last iteration

      with function F (X : Element_In; I : Element_Out) return Element_Out;
      --  Function that should be applied to elements of Array_Type

   package Fold_2_Acc is
      pragma Annotate (GNATprove, Terminating, Fold_2_Acc);

      procedure Prove_Ind_Col
        (A : Array_Type; X : Element_Out; I : Index_1; J : Index_2)
      with
        Ghost,
        Pre  => I in A'Range (1) and then J in A'Range (2)
        and then J /= A'Last (2) and then Ind_Prop (A, X, I, J),
        Post => Ind_Prop (A, F (A (I, J), X), I, J + 1);
      --  Axiom: Ind_Prop should be preserved when going to next column

      procedure Prove_Ind_Row (A : Array_Type; X : Element_Out; I : Index_1)
      with
        Ghost,
        Pre  => I in A'Range (1) and then A'Length (2) > 0
        and then I /= A'Last (1) and then Ind_Prop (A, X, I, A'Last (2)),
        Post => Ind_Prop (A, F (A (I, A'Last (2)), X), I + 1, A'First (2));
      --  Axiom: Ind_Prop should be preserved when going to next row

      procedure Prove_Last (A : Array_Type; X : Element_Out) with
        Ghost,
        Pre  => A'Length (1) > 0 and then A'Length (2) > 0
        and then Ind_Prop (A, X, A'Last (1), A'Last (2)),
        Post => Final_Prop (A, F (A (A'Last (1), A'Last (2)), X));
      --  Axiom: Final_Prop should be provable at the last iteration from
      --  Ind_Prop.

      type Acc_Array is array (Index_1 range <>, Index_2 range <>)
        of Element_Out;

      function Fold (A : Array_Type; Init : Element_Out) return Acc_Array with
        Pre  => A'Length (1) > 0 and then A'Length (2) > 0
        and then Ind_Prop (A, Init, A'First (1), A'First (2)),
        Post => Fold'Result'First (1) = A'First (1)
        and then Fold'Result'Last (1) = A'Last (1)
        and then Fold'Result'First (2) = A'First (2)
        and then Fold'Result'Last (2) = A'Last (2)
        and then Ind_Prop (A, Init, A'First (1), A'First (2))
        and then Fold'Result (A'First (1), A'First (2)) =
          F (A (A'First (1), A'First (2)), Init)
        and then
          (for all I in A'Range (1) =>
             (if I > A'First (1) then
                  Ind_Prop (A, Fold'Result (I - 1, A'Last (2)), I, A'First (2))
              and then Fold'Result (I, A'First (2)) =
                  F (A (I, A'First (2)), Fold'Result (I - 1, A'Last (2)))))
        and then
          (for all I in A'Range (1) =>
             (for all J in A'Range (2) =>
                  (if J > A'First (2) then
                         Ind_Prop (A, Fold'Result (I, J - 1), I, J)
                   and then Fold'Result (I, J) =
                         F (A (I, J), Fold'Result (I, J - 1)))))
        and then Final_Prop (A, Fold'Result (A'Last (1), A'Last (2)));
   end Fold_2_Acc;

   generic
      type Index_1 is range <>;
      type Index_2 is range <>;
      type Element_In is private;
      type Array_Type is array (Index_1 range <>, Index_2 range <>)
        of Element_In;
      type Element_Out is private;
      with function Ind_Prop
        (A : Array_Type;
         X : Element_Out;
         I : Index_1;
         J : Index_2) return Boolean;
      --  Potential inductive property that should be maintained during fold

      with function Final_Prop
        (A : Array_Type;
         X : Element_Out) return Boolean;
      --  Potential inductive property at the last iteration

      with function F (X : Element_In; I : Element_Out) return Element_Out;
      --  Function that should be applied to elements of Array_Type

   package Fold_2 is
      pragma Annotate (GNATprove, Terminating, Fold_2);

      package Acc is new Fold_2_Acc
        (Index_1     => Index_1,
         Index_2     => Index_2,
         Element_In  => Element_In,
         Array_Type  => Array_Type,
         Element_Out => Element_Out,
         Ind_Prop    => Ind_Prop,
         Final_Prop  => Final_Prop,
         F           => F);

      function Fold (A : Array_Type; Init : Element_Out) return Element_Out
      with
        Pre  => A'Length (1) = 0 or else A'Length (2) = 0
        or else Ind_Prop (A, Init, A'First (1), A'First (2)),
        Post =>
          (if A'Length (1) = 0 or else A'Length (2) = 0 then Fold'Result = Init
           else Fold'Result = Acc.Fold (A, Init) (A'Last (1), A'Last (2))
           and then Final_Prop (A, Fold'Result));
   end Fold_2;

   generic
      type Index_1 is range <>;
      type Index_2 is range <>;
      type Element_In is private;
      type Array_Type is array (Index_1 range <>, Index_2 range <>)
        of Element_In;
      type Element_Out is range <>;

      with function Value (X : Element_In) return Element_Out;
      --  Sum the value of each element
   package Sum_2 is
      pragma Annotate (GNATprove, Terminating, Sum_2);

      function In_Range
        (A : Array_Type; X : Element_Out'Base; I : Index_1; J : Index_2)
         return Boolean
      is (X in Element_Out'First *
          (Element_Out'Base (I - A'First (1)) * A'Length (2)
           + Element_Out'Base (J - A'First (2))) ..
            Element_Out'Last *
              (Element_Out'Base (I - A'First (1)) * A'Length (2)
               + Element_Out'Base (J - A'First (2))))
      with Ghost,
        Pre => I in A'Range (1) and then J in A'Range (2),
        Post =>
          (if In_Range'Result then
             X in
               Element_Out'Base'First -
                 Element_Out'Min (0, Element_Out'First) ..
               Element_Out'Base'Last - Element_Out'Max (0, Element_Out'Last));

      function Result_In_Range
        (A : Array_Type; X : Element_Out'Base) return Boolean
      is
        (X in
           Element_Out'First * A'Length (1) * A'Length (2) ..
             Element_Out'Last * A'Length (1) * A'Length (2));

      function Add_Value (X : Element_In; Y : Element_Out'Base) return
        Element_Out'Base
      is (Value (X) + Y)
      with Pre => Y in
          Element_Out'Base'First - Element_Out'Min (0, Element_Out'First) ..
        Element_Out'Base'Last - Element_Out'Max (0, Element_Out'Last),
        Post => Add_Value'Result = (Value (X) + Y);
      pragma Annotate (GNATprove, Inline_For_Proof, Add_Value);

      package Fold_Sum is new Fold_2
        (Index_1     => Index_1,
         Index_2     => Index_2,
         Element_In  => Element_In,
         Array_Type  => Array_Type,
         Element_Out => Element_Out'Base,
         Ind_Prop    => In_Range,
         Final_Prop  => Result_In_Range,
         F           => Add_Value);

      function Sum (A : Array_Type) return Element_Out'Base is
        (Fold_Sum.Fold (A, 0));

      procedure Update_Sum (A1, A2 : Array_Type; I : Index_1; J : Index_2)
      with Ghost,
        Pre  => I in A1'Range (1) and then J in A1'Range (2) and then
        A1'First (1) = A2'First (1) and then A1'Last (1) = A2'Last (1) and then
        A1'First (2) = A2'First (2) and then A1'Last (2) = A2'Last (2) and then
        (for all K in A1'Range (1) =>
           (for all L in A2'Range (2) =>
              (if K /= I or else L /= J then A1 (K, L) = A2 (K, L)))),
        Post => Sum (A2) - Value (A2 (I, J)) = Sum (A1) - Value (A1 (I, J));
      --  Lemma: Modification of Sum after an update to the array

      procedure Sum_Cst (A : Array_Type; C : Element_Out) with Ghost,
        Post => (if (for all I in A'Range (1) =>
                   (for all J in A'Range (2) => Value (A (I, J)) = C)) then
                     Sum (A) = C * A'Length (1) * A'Length (2));
      --  Lemma: Value of Sum on a constant array

   end Sum_2;

   generic
      type Index_1 is range <>;
      type Index_2 is range <>;
      type Element is private;
      type Array_Type is array (Index_1 range <>, Index_2 range <>)
        of Element;
      with function Choose (X : Element) return Boolean;
      --  Count the number of elements for which Choose return True

   package Count_2 is
      pragma Annotate (GNATprove, Terminating, Count_2);

      function In_Range
        (A : Array_Type; X : Natural; I : Index_1; J : Index_2) return Boolean
      is
        (X <= Natural (I - A'First (1)) * A'Length (2)
         + Natural (J - A'First (2)))
      with Ghost,
        Pre  => I in A'Range (1) and then J in A'Range (2),
        Post => (if In_Range'Result then X < Integer'Last);

      function Add_One (E : Element; X : Natural) return Natural
      is (if Choose (E) then X + 1 else X)
      with Pre => X < Integer'Last,
        Post => Add_One'Result = (if Choose (E) then X + 1 else X);
      pragma Annotate (GNATprove, Inline_For_Proof, Add_One);

      function Result_In_Range
        (A : Array_Type; X : Natural) return Boolean
      is (X <= A'Length (1) * A'Length (2));

      package Fold_Count is new Fold_2
        (Index_1     => Index_1,
         Index_2     => Index_2,
         Element_In  => Element,
         Array_Type  => Array_Type,
         Element_Out => Natural,
         Ind_Prop    => In_Range,
         Final_Prop  => Result_In_Range,
         F           => Add_One);

      function Count (A : Array_Type) return Natural is
        (Fold_Count.Fold (A, 0));

      procedure Update_Count (A1, A2 : Array_Type; I : Index_1; J : Index_2)
      with Ghost,
        Pre => I in A1'Range (1) and then J in A1'Range (2) and then
        A1'First (1) = A2'First (1) and then A1'Last (1) = A2'Last (1) and then
        A1'First (2) = A2'First (2) and then A1'Last (2) = A2'Last (2) and then
        (for all K in A1'Range (1) =>
           (for all L in A2'Range (2) =>
              (if K /= I or else L /= J then A1 (K, L) = A2 (K, L)))),
        Contract_Cases =>
          (Choose (A1 (I, J)) = Choose (A2 (I, J))
           =>
             Count (A1) = Count (A2),
           Choose (A1 (I, J)) and not Choose (A2 (I, J))
           =>
             Count (A1) = Count (A2) + 1,
           not Choose (A1 (I, J)) and Choose (A2 (I, J))
           =>
             Count (A1) + 1 = Count (A2));
      --  Lemma: Modification of Count after an update to the array

      procedure Count_Zero (A : Array_Type) with Ghost,
        Post => (Count (A) = 0) =
          (for all I in A'Range (1) =>
             (for all J in A'Range (2) => not Choose (A (I, J))));
      --  Lemma: Count returns 0 if and only if no element is chosen

   end Count_2;

end SPARK.Higher_Order.Fold;
