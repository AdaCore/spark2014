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

end Higher_Order;
