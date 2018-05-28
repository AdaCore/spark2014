package Higher_Order with SPARK_Mode is

   generic
      type Index_Type is range <>;
      type Element_In is private;
      type Array_In is array (Index_Type range <>) of Element_In;
      type Element_Out is private;
      type Array_Out is array (Index_Type range <>) of Element_Out;
      with function Init_Prop (A : Element_In) return Boolean;
      --  Potential additional constraint on values of the array to allow Map

      with function F (X : Element_In) return Element_Out;
      --  Function that should be applied to elements of Array_In

   function Map (A : Array_In) return Array_Out with
     Pre  => (for all I in A'Range => Init_Prop (A (I))),
     Post => Map'Result'First = A'First
     and then Map'Result'Last = A'Last
     and then (for all I in A'Range =>
                 Map'Result (I) = F (A (I)));

   generic
      type Index_Type is range <>;
      type Element_In is private;
      type Array_In is array (Index_Type range <>) of Element_In;
      type Element_Out is private;
      type Array_Out is array (Index_Type range <>) of Element_Out;
      with function Init_Prop (I : Index_Type; A : Element_In) return Boolean;
      --  Potential additional constraint on values of the array to allow Map

      with function F (I : Index_Type; X : Element_In) return Element_Out;
      --  Function that should be applied to elements of Array_In

   function Map_I (A : Array_In) return Array_Out with
     Pre  => (for all I in A'Range => Init_Prop (I, A (I))),
     Post => Map_I'Result'First = A'First
     and then Map_I'Result'Last = A'Last
     and then (for all I in A'Range =>
                 Map_I'Result (I) = F (I, A (I)));

   generic
      type Index_Type is range <>;
      type Element is private;
      type Array_Type is array (Index_Type range <>) of Element;
      with function Init_Prop (A : Element) return Boolean;
      --  Potential additional constraint on values of the array to allow Map

      with function F (X : Element) return Element;
      --  Function that should be applied to elements of Array_Type

   procedure Map_Proc (A : in out Array_Type) with
     Pre  => (for all I in A'Range => Init_Prop (A (I))),
     Post => (for all I in A'Range => A (I) = F (A'Old (I)));

   generic
      type Index_Type is range <>;
      type Element is private;
      type Array_Type is array (Index_Type range <>) of Element;
      with function Init_Prop (I : Index_Type; A : Element) return Boolean;
      --  Potential additional constraint on values of the array to allow Map

      with function F (I : Index_Type; X : Element) return Element;
      --  Function that should be applied to elements of Array_In

   procedure Map_I_Proc (A : in out Array_Type) with
     Pre  => (for all I in A'Range => Init_Prop (I, A (I))),
     Post => (for all I in A'Range => A (I) = F (I, A'Old (I)));

end Higher_Order;
