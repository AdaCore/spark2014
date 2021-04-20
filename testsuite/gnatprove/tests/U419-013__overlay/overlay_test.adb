package body Overlay_Test is
   procedure Test_Program (A : aliased Nv_DW_Block64) is
      B : constant Nv_B_Block64 with
         Address=> A'Address, Import, Alignment => 4;
   begin
      null;
   end Test_Program;

end Overlay_Test;
