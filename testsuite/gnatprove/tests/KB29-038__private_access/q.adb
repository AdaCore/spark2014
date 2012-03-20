package body Q is
   procedure Proc (X : T1; Y, Z : in out Integer) is
     Tmp : Integer range 1 .. 10;
   begin
      Log (Get_My_T2 (X));
      Tmp := Y;
      Y := Z;
      Z := tmp;
   end Proc;
end Q;
