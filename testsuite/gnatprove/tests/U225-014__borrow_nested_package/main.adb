procedure Main with SPARK_Mode is
   generic
   package Gen_Nested is
      procedure Do_Something;
   end Gen_Nested;
   package body Gen_Nested is
      type Int_Acc is access Integer;
      type Holder is record
         C : Int_Acc;
      end record;

      V : Holder;

      procedure Do_Something is
      begin
         if V.C /= null then
            V.C.all := 0;
         end if;
      end Do_Something;
   end Gen_Nested;

   package Nested is new Gen_Nested;
begin
   Nested.Do_Something;
end Main;
