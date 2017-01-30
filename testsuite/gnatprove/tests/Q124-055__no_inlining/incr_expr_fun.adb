package body Incr_Expr_Fun
  with SPARK_Mode
is
   function Incr_Pub_Body (X : Integer) return Integer is (X + 1);

   function Incr_Priv_Body (X : Integer) return Integer is (X + 1);

   function Incr_Body (X : Integer) return Integer is (X + 1);

   function Incr_Body_Body (X : Integer) return Integer;
   function Incr_Body_Body (X : Integer) return Integer is (X + 1);

   procedure Test is
      X : Integer := 10;
   begin
      pragma Assert (Incr_Pub (X) = X + 1);
      pragma Assert (Incr_Pub_Pub (X) = X + 1);
      pragma Assert (Incr_Pub_Priv (X) = X + 1);
      pragma Assert (Incr_Pub_Body (X) = X + 1);
      pragma Assert (Incr_Priv (X) = X + 1);
      pragma Assert (Incr_Priv_Priv (X) = X + 1);
      pragma Assert (Incr_Priv_Body (X) = X + 1);
      pragma Assert (Incr_Body (X) = X + 1);
      pragma Assert (Incr_Body_Body (X) = X + 1);
   end Test;

end Incr_Expr_Fun;
