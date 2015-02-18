package Stack with SPARK_Mode is
   Max : constant Natural := 100;
   subtype Less_Than_Max is Natural range 0 .. Max;

   type Element is new Natural;
   type Stack_Root is abstract tagged private;

   function Size (S : Stack_Root'Class) return Less_Than_Max;

private
   type Element_Array is array (Positive range 1 .. Max) of Element;
   type Stack_Root is abstract tagged record
      Content : Element_Array;
      Length  : Less_Than_Max;
   end record;
   function Size (S : Stack_Root'Class) return Less_Than_Max is (S.Length);
end Stack;
