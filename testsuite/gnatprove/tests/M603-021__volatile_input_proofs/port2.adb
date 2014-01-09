package body Port2
is
   procedure Test_Eval_Order_OK (X : out Boolean)
   is
      T1 : Integer;
      T2 : Integer;
   begin
      T1 := V1;
      T2 := V1;

      -- No order dependence, so OK
      X := (T1 <= T2);
   end Test_Eval_Order_OK;

end Port2;
