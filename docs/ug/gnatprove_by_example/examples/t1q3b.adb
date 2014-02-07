package body T1Q3B
  with SPARK_Mode
is

   procedure NandGate (P, Q : in Boolean; R : out Boolean) is
   begin
      R := not (P and Q);
   end NandGate;

end T1Q3B;
