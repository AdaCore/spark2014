package body Test_Acc with SPARK_Mode is

   --  Marking this overlay used to touch the fields of Outer and Inner, and
   --  follow the access-to-constant component into its designated type.

   procedure Q (D : aliased in out Buf) is
      Ov : Outer with Import, Address => D'Address;
   begin
      D (1) := 0;
   end Q;
end Test_Acc;
