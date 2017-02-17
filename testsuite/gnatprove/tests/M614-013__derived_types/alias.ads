package Alias is
   subtype Element is Integer range 0 .. 100;
   type My_Rec is record
      Content : Element := 0;
      Modulus : Natural := 0;
   end record;

   function Get_Content (R : My_Rec) return Element with
     Pre => R.Modulus > 0;

   type My_Alias is new My_Rec;

   function Add (R : My_Alias; X : Element) return Integer with
     Post => Add'Result = Get_Content (R) + X;
end Alias;
