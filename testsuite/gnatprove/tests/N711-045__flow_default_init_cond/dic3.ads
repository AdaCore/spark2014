package Dic3 is
   type Root_T is private
     with Default_Initial_Condition => To_Int (Root_T) = 5;

   type Derived_T is private
     with Default_Initial_Condition => To_Int (Derived_T) in 1 .. 10;

   function To_Int (R : Root_T) return Integer;

   function To_Int (D : Derived_T) return Integer;

   procedure Test;
private
   type Root_T is new Integer
     with Default_Value => 5;

   type Derived_T is new Root_T;
end Dic3;
