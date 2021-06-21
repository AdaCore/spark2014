procedure Test_Access_Ownership_Error with SPARK_Mode is
   type Rec is record
      F1, F2 : aliased Integer;
   end record;

   function F_Obs (X : Rec) return not null access constant Integer with
     Import;

   function F_Bor (X : not null access Rec) return not null access Integer with
     Import;

   V : aliased Rec := (1, 2);
begin
   --  observe

   declare
      Obs_1 : access constant Integer := V.F1'Access;
   begin
      V.F1 := 15;
   end;

   declare
      Obs_3 : access constant Integer := F_Obs (V);
   begin
      V.F1 := 15;
      V.F2 := 15;
   end;

   --  borrow

   declare
      B_1 : access Integer := V.F1'Access;
   begin
      V.F1 := 15;
   end;
   pragma Assert (V.F1 = 4);

   declare
      V_B : constant access Rec := V'Access;
      B_3 : access Integer := F_Bor (V_B);
   begin
      V.F1 := 15;
      V_B.F1 := 15;
      V.F2 := 15;
   end;
end Test_Access_Ownership_Error;
