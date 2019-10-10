package Foo with SPARK_Mode is
   type T is private;
   C : constant T;
   procedure Inc;
   function Get return Integer;
private
   type Int_Acc is access Integer;
   type T is record
      F : Int_Acc;
   end record;
   C_F : constant Int_Acc := new Integer'(0);
   C : constant T := (F => C_F);
end;
