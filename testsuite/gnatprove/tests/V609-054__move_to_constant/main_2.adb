procedure Main_2 with SPARK_Mode is

   type Int_Acc is access Integer;
   type R is record
      F : Int_Acc;
   end record;
   type C_Acc is access constant R;

   A : aliased constant R := (F => new Integer'(17));
   B : constant R := A;
begin
   null;
end Main_2;
