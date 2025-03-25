procedure Main with SPARK_Mode is
   type Int_Acc is access Integer;
   type Int_Acc_Array is array (Integer range 0 .. 10) of Int_Acc;
   X : Int_Acc_Array := (0 .. 10 => new Integer'(0));
   Y : Int_Acc := X (1 .. 1) (1);
   Z : Int_Acc := X (2 .. 3) (2);
begin
   null;
end Main;