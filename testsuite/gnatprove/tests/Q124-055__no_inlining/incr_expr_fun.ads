package Incr_Expr_Fun
  with SPARK_Mode
is
   function Incr_Pub (X : Integer) return Integer is (X + 1);

   function Incr_Pub_Pub (X : Integer) return Integer;
   function Incr_Pub_Pub (X : Integer) return Integer is (X + 1);

   function Incr_Pub_Priv (X : Integer) return Integer;

   function Incr_Pub_Body (X : Integer) return Integer;

   procedure Test;
private
   function Incr_Pub_Priv (X : Integer) return Integer is (X + 1);

   function Incr_Priv (X : Integer) return Integer is (X + 1);

   function Incr_Priv_Priv (X : Integer) return Integer;
   function Incr_Priv_Priv (X : Integer) return Integer is (X + 1);

   function Incr_Priv_Body (X : Integer) return Integer;
end Incr_Expr_Fun;
