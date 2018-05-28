package Higher_Order.Fold with SPARK_Mode is

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

      with function F (X : Element_In; I : Element_Out) return Element_Out;
      --  Function that should be applied to elements of Array_Type

   package Fold_Left_Acc is
      type Acc_Array is array (Index_Type range <>) of Element_Out;

      function Prev_Val
        (Acc  : Acc_Array;
         I    : Index_Type;
         Init : Element_Out) return Element_Out
      is
        (if I = Acc'First then Init else Acc (I - 1))
      with Ghost,
         Pre => I in Acc'Range;

      function Fold (A : Array_Type; Init : Element_Out) return Acc_Array with
        Pre  => A'Length > 0 and then Ind_Prop (A, Init, A'First),
        Post => Fold'Result'First = A'First
        and then Fold'Result'Last = A'Last
        and then (for all I in A'Range =>
                    Ind_Prop (A, Prev_Val (Fold'Result, I, Init), I)
                  and then Fold'Result (I) =
                      F (A (I), Prev_Val (Fold'Result, I, Init)));
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

      with function F (X : Element_In; I : Element_Out) return Element_Out;
      --  Function that should be applied to elements of Array_Type

   package Fold_Left is
      package Acc is new Fold_Left_Acc
        (Index_Type  => Index_Type,
         Element_In  => Element_In,
         Array_Type  => Array_Type,
         Element_Out => Element_Out,
         Ind_Prop    => Ind_Prop,
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

      with function F (X : Element_In; I : Element_Out) return Element_Out;
      --  Function that should be applied to elements of Array_Type

   package Fold_Right_Acc is
      type Acc_Array is array (Index_Type range <>) of Element_Out;

      function Prev_Val
        (Acc  : Acc_Array;
         I    : Index_Type;
         Init : Element_Out) return Element_Out
      is
        (if I = Acc'Last then Init else Acc (I + 1))
      with Ghost,
         Pre => I in Acc'Range;

      function Fold (A : Array_Type; Init : Element_Out) return Acc_Array with
        Pre  => A'Length > 0 and then Ind_Prop (A, Init, A'Last),
        Post => Fold'Result'First = A'First
        and then Fold'Result'Last = A'Last
        and then (for all I in A'Range =>
                    Ind_Prop (A, Prev_Val (Fold'Result, I, Init), I)
                  and then Fold'Result (I) =
                      F (A (I), Prev_Val (Fold'Result, I, Init)));
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

      with function F (X : Element_In; I : Element_Out) return Element_Out;
      --  Function that should be applied to elements of Array_Type

   package Fold_Right is
      package Acc is new Fold_Right_Acc
        (Index_Type  => Index_Type,
         Element_In  => Element_In,
         Array_Type  => Array_Type,
         Element_Out => Element_Out,
         Ind_Prop    => Ind_Prop,
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
      type Element is range <>;
      type Array_Type is array (Index_Type range <>) of Element;
   package Sum is
      function In_Range
        (A : Array_Type; X : Element'Base; I : Index_Type) return Boolean
      is (X in Element'First * Element'Base (I - A'First) ..
            Element'Last * Element'Base (I - A'First))
      with Ghost,
        Pre => I in A'Range;

      package Sum_Left is new Fold_Left
        (Index_Type  => Index_Type,
         Element_In  => Element,
         Array_Type  => Array_Type,
         Element_Out => Element'Base,
         Ind_Prop    => In_Range,
         F           => "+");

      function Sum (A : Array_Type) return Element'Base is
        (Sum_Left.Fold (A, 0))
      with Post => Sum'Result in
            Element'First * A'Length .. Element'Last * A'Length;
   end Sum;

   generic
      type Index_Type is range <>;
      type Element is private;
      type Array_Type is array (Index_Type range <>) of Element;
      with function Choose (X : Element) return Boolean;
   package Count is
      function In_Range
        (A : Array_Type; X : Natural; I : Index_Type) return Boolean
      is (X <= Natural (I - A'First))
      with Ghost,
        Pre => I in A'Range;

      function Add_One (E : Element; X : Natural) return Natural
      is (if Choose (E) then X + 1 else X)
      with Pre => X < Integer'Last;

      package Count_Left is new Fold_Left
        (Index_Type  => Index_Type,
         Element_In  => Element,
         Array_Type  => Array_Type,
         Element_Out => Natural,
         Ind_Prop    => In_Range,
         F           => Add_One);

      function Count (A : Array_Type) return Natural is
        (Count_Left.Fold (A, 0))
      with Post => Count'Result <= A'Length;
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

      with function F (X : Element_In; I : Element_Out) return Element_Out;
      --  Function that should be applied to elements of Array_Type

   package Fold_2 is
      type Acc_Array is array (Index_1 range <>, Index_2 range <>)
        of Element_Out
      with Ghost;

      function Prev_Val
        (Acc  : Acc_Array;
         I    : Index_1;
         J    : Index_2;
         Init : Element_Out) return Element_Out
      is
        (if I = Acc'First (1) and then J = Acc'First (2) then Init
         elsif J = Acc'First (2) then Acc (I - 1, Acc'Last (2))
         else Acc (I, J - 1))
      with Ghost,
         Pre => I in Acc'Range (1) and then J in Acc'Range (2);

      function Acc_F (A : Array_Type; Init : Element_Out) return Acc_Array with
        Ghost,
        Pre  => A'Length (1) > 0 and then A'Length (2) > 0
        and then Ind_Prop (A, Init, A'First (1), A'First (2)),
        Post => Acc_F'Result'First (1) = A'First (1)
        and then Acc_F'Result'Last (1) = A'Last (1)
        and then Acc_F'Result'First (2) = A'First (2)
        and then Acc_F'Result'Last (2) = A'Last (2)
        and then
          (for all I in A'Range (1) =>
             (for all J in A'Range (2) =>
                  Ind_Prop (A, Prev_Val (Acc_F'Result, I, J, Init), I, J)
              and then Acc_F'Result (I, J) =
                  F (A (I, J), Prev_Val (Acc_F'Result, I, J, Init))));

      function Fold (A : Array_Type; Init : Element_Out) return Element_Out
      with
        Pre  => A'Length (1) = 0 or else A'Length (2) = 0
        or else Ind_Prop (A, Init, A'First (1), A'First (2)),
        Post => Fold'Result =
          (if A'Length (1) = 0 or else A'Length (2) = 0 then Init
           else Acc_F (A, Init) (A'Last (1), A'Last (2)));
   end Fold_2;

end Higher_Order.Fold;
