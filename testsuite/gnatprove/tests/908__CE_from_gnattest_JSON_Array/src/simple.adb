package body Simple
with SPARK_Mode
is

   function Add_Array (A : My_Array) return T is
      Toto : T := 0;
   begin
      for Elt in A'Range loop
         Toto := Toto + A (Elt);
      end loop;
      return Toto;
   end Add_Array;

   procedure Check_Family (F : Family) is
      Total_Age : Integer := 0;
   begin
      for N in F'Range loop
         pragma Assert (F (N).Age /= 22);
      end loop;
   end Check_Family;

end Simple;
