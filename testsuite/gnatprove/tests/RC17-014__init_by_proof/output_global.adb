procedure Output_Global with SPARK_Mode is
   type My_Nat is new Integer range 10 .. 150 with
     Relaxed_Initialization;

   G : My_Nat;

   procedure P5 with Global => (Output => G) is
   begin
      null;
   end;
begin
   P5;
end Output_Global;
