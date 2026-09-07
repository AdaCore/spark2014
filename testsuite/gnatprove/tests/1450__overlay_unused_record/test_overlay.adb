package body Test_Overlay with SPARK_Mode is

   --  Overlaying a record type whose nested record fields are never touched
   --  in this unit used to send gnat2why into an infinite recursion when
   --  computing the size of the components of Outer.

   procedure Q (D : aliased out Buf) is
      Ov : Outer with Import, Address => D'Address;
   begin
      D := (others => 0);
   end Q;
end Test_Overlay;
