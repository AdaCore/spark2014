package Dic2 is
   type T is private
     with Default_Initial_Condition => Foo (T);

   type U is private
     with Default_Initial_Condition => Bar (U);

   type R is record
      X : T;
      Y : U;
   end record;

   function Foo (Par : T) return Boolean;

   function Bar (Par : U) return Boolean;

   procedure Test;
private
   type T is new Integer
     with Default_Value => 0;

   type U is new Integer
     with Default_Value => 1;
end Dic2;
