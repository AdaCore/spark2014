package Stack with SPARK_Mode is
   type Element is new Natural;
   type Stack is private;

   function Empty return Stack;
   procedure Push (S : in out Stack; E : Element);
   function Pop (S : in out Stack) return Element;
private
   type Element_Array is array (Positive range <>) of Element;
   Max : constant := 100;
   subtype Top_Range is Natural range 1 .. Max;
   type Stack is record
      Content : Element_Array (1 .. Max);
      Top     : Top_Range;
   end record;
end Stack;
