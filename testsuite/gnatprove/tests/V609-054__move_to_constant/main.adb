procedure Main with SPARK_Mode is

   type Int_Acc is access Integer;
   type R is record
      F : Int_Acc;
   end record;
   type C_Acc is access constant R;

   D : aliased constant R := (F => new Integer'(17));
   E : C_Acc := new R'(D);
   F : constant R := E.all;
begin
   null;
end Main;
