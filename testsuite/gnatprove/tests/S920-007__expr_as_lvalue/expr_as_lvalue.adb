procedure Expr_As_Lvalue (B : Boolean) with SPARK_Mode is
   type AI is access Integer;

   procedure Test (x : in out Integer) with Import;

   X : AI := new Integer'(44);
   Y : AI := new Integer'(15);
begin
   AI'(if B then X else Y).all := 5;

   Test (AI'(if B then X else Y).all);
end Expr_As_Lvalue;
