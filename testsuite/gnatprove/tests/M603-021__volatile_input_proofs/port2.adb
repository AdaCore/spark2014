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


   procedure Test_Eval_Order_Bad1 (X : out Boolean)
   is
      T1 : Integer;
   begin
      T1 := V1; -- OK

      -- No order dependence here, but violates LRM 7.1.3(13),
      -- so illegal
      X := (T1 <= V1);
   end Test_Eval_Order_Bad1;


   procedure Test_Eval_Order_Bad2 (X : out Boolean)
   is
   begin
      -- order dependence, and definitely violates 7.1.3(13),
      -- so illegal
      X := (V1 <= V1);
   end Test_Eval_Order_Bad2;

end Port2;
