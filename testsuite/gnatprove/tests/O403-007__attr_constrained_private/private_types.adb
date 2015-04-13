package body Private_Types with SPARK_Mode => Off is

   procedure Private_ReInit (S : in out Simple) is
   begin
      S := (D => 0, F1 => null);
   end Private_ReInit;
end Private_Types;
