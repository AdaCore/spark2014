package Varinput with
  SPARK_Mode
is
   type T1 is private;
   type T2 is private;
private
   G : Boolean := True;
   function F return Boolean is (G);
   type T1 is new Integer with
     Type_Invariant => F;
   type T2 is new Integer with
     Predicate => F;
end Varinput;
