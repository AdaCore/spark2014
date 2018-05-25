package Higher_Order with SPARK_Mode is

   generic
      type Index_Type is range <>;
      type Element_1 is private;
      type Array_1 is array (Index_Type range <>) of Element_1;
      type Element_2 is private;
      type Array_2 is array (Index_Type range <>) of Element_2;
      with function F (X : Element_1) return Element_2;
      --  Function that should be applied to elements of Array_1

   function Map_F (A : Array_1) return Array_2 with
     Post => Map_F'Result'First = A'First
     and then Map_F'Result'Last = A'Last
     and then (for all I in A'Range =>
                 Map_F'Result (I) = F (A (I)));

   generic
      type Index_Type is range <>;
      type Element is private;
      type Array_Type is array (Index_Type range <>) of Element;
      with function Init_Prop (A : Element) return Boolean;
      --  Potential additional constraint on values of the array to allow Map

      with function F (X : Element) return Element;
      --  Function that should be applied to elements of Array_Type

   procedure Proc_Map_F (A : in out Array_Type) with
     Pre  => (for all I in A'Range => Init_Prop (A (I))),
     Post => (for all I in A'Range => A (I) = F (A'Old (I)));

   generic
      type Index_Type is range <>;
      type Element_1 is private;
      type Array_Type is array (Index_Type range <>) of Element_1;
      type Element_2 is private;
      with function Ind_Prop
        (A     : Array_Type;
         X     : Element_2;
         Count : Natural) return Boolean;
      --  Potential inductive property that should be maintained during fold

      with function F (X : Element_1; I : Element_2) return Element_2;
      --  Function that should be applied to elements of Array_Type

   package Fold is
      type Acc_Array is array (Index_Type range <>) of Element_2 with Ghost;
      function Acc_F (A : Array_Type; Init : Element_2) return Acc_Array with
        Ghost,
        Pre  => Ind_Prop (A, Init, 0),
        Post => Acc_F'Result'First = A'First
        and then Acc_F'Result'Last = A'Last
        and then (for all I in A'Range =>
                    Ind_Prop (A, Acc_F'Result (I), Natural (I - A'First) + 1)
                  and then Acc_F'Result (I) =
                      F (A (I),
                         (if I = A'First then Init
                            else Acc_F'Result (I - 1))));

      function Fold_F (A : Array_Type; Init : Element_2) return Element_2 with
        Pre  => Ind_Prop (A, Init, 0),
        Post => Fold_F'Result =
          (if A'Length = 0 then Init
           else Acc_F (A, Init) (A'Last));
      end Fold;

   generic
      type Index_1 is range <>;
      type Index_2 is range <>;
      type Element_1 is private;
      type Array_Type is array (Index_1, Index_2) of Element_1;
      type Element_2 is private;
      with function Ind_Prop
        (A      : Array_Type;
         X      : Element_2;
         Count1 : Natural;
         Count2 : Natural) return Boolean;
      --  Potential inductive property that should be maintained during fold

      with function F (X : Element_1; I : Element_2) return Element_2;
      --  Function that should be applied to elements of Array_Type

   package Fold_2 is
      type Acc_Array is array (Index_1, Index_2) of Element_2 with Ghost;

      function Prev_Val (Acc : Acc_Array; I : Index_1; J : Index_2; Init : Element_2) return Element_2 is
        (if I = Acc'First (1) and then J = Acc'First (2) then Init
         elsif J = Acc'First (2) then Acc (I - 1, Acc'Last (2))
         else Acc (I, J - 1)) with Ghost;

      function Acc_F (A : Array_Type; Init : Element_2) return Acc_Array with
        Ghost,
        Pre  => Ind_Prop (A, Init, 0, 0),
        Post =>
          (for all I in A'Range (1) =>
             (for all J in A'Range (2) =>
                  Ind_Prop (A, Acc_F'Result (I, J),
                Natural (I - A'First (1)) + 1,
                Natural (J - A'First (2)) + 1)
              and then Acc_F'Result (I, J) =
                  F (A (I, J), Prev_Val (Acc_F'Result, I, J, Init))));

      function Fold_F (A : Array_Type; Init : Element_2) return Element_2 with
        Pre  => Ind_Prop (A, Init, 0, 0),
        Post => Fold_F'Result =
          (if A'Length (1) = 0 or else A'Length (2) = 0 then Init
           else Acc_F (A, Init) (A'Last (1), A'Last (2)));
   end Fold_2;

end Higher_Order;
