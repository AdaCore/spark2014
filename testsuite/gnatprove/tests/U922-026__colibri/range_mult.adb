procedure Range_Mult is
   type Float_32 is new Float;

   procedure P (X : Float_32; Res : out Float_32)
     with Post => True
   is
   begin
      pragma Assume (X in 5.0 .. 10.0);
      Res := X * 2.0 - 5.0;
      pragma Assert (Res > X); --@ASSERT:FAIL
   end P;
begin
   null;
end;
