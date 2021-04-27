package body Volatile_Access with SPARK_Mode Is
   procedure P is
      B : access Integer := X'Access;
      C : constant Integer := B.all;
   begin
      pragma Assert (B.all = C); -- This should not prove!
   end P;
end Volatile_Access;
