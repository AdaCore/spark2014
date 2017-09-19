package body Resources
  with SPARK_Mode
is
   procedure Create (D : out Data) is
   begin
      for J in D'Range loop
         D(J) := J;
         --  pragma Loop_Invariant (2 * Sum (D, J) <= J * (J + 1));
      end loop;
   end Create;

   procedure Remove (D : in out Data; J : Index) is
   begin
     D (J) := 0;
   end Remove;

end Resources;
