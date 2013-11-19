package body P
  with SPARK_Mode
is
   procedure Init (X : out A) is
   begin
      X := (1 => X'Last, 20 => -1, others => 0);
   end Init;
end P;
