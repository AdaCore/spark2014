package body Predicate
with SPARK_Mode
is
   procedure P1 (P : in out P_Type)
   is
   begin
      pragma Assert (P'Length > 2);
      P (P'First) := 'x';
   end P1;

   procedure P2 (P : out P_Type)
   is
   begin
      pragma Assert (P'Length > 2);
      P := (others => 'x');
   end P2;
end Predicate;
