package body P
with SPARK_Mode
is

   procedure Execute (X : in Integer;
                      Y : out Integer) is
   begin
      Y := X;
   end Execute;

end P;
