package body Bounded with
  SPARK_Mode
is

   procedure Test is
      V : Vector (2);
   begin
      Append (V, 1);
      Append (V, 2);
      Append (V, 3);
   end Test;

end Bounded;
