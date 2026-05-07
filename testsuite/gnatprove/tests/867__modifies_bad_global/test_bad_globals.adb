procedure Test_Bad_Globals with SPARK_Mode is
   A : Integer;

   --  We reject objects if they are not outputs of the subprogram

   procedure Reset_Bad_Global (G : Boolean) with
     Modifies => (A when G);

   procedure Reset_Bad_Global (G : Boolean) is
   begin
      null;
   end Reset_Bad_Global;

   --  Overlays, only the ultimate underlying object can be mentioned

   X : Integer;
   Y : Integer with Address => X'Address, Import;

   procedure P with
     Modifies => Y
   is
   begin
      Y := 13;
   end P;

begin
   null;
end;
