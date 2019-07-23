procedure Output_Global with SPARK_Mode is
   subtype My_Nat is Integer range 10 .. 150;
   pragma Annotate (GNATprove, Init_By_Proof, My_Nat);

   G : My_Nat;

   procedure P5 with Global => (Output => G) is
   begin
      null;
   end;
begin
   P5;
end Output_Global;
