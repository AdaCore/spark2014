package P is
   type T1 is private;
   type T2 is private;

   function Get_My_T2 (X : T1) return T2;
   procedure Log (X : T2);

private
   pragma SPARK_Mode (Off);

   type R2 is record
      Component : Integer;
   end record;
   type T2 is access R2;
   type R1 is record
      My_T2 : T2;
   end record;
   type T1 is access R1;

   function Get_My_T2 (X : T1) return T2 is (X.My_T2);
end P;
