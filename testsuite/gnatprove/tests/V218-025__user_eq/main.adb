procedure Main with SPARK_Mode is
   type Use_User_Eq is record
      F, G : Integer;
   end record;
   function "=" (X, Y : Use_User_Eq) return Boolean is (X.F = Y.F);

   package Private_Types is
      type Rec is private;
      C1 : constant Rec;
      C2 : constant Rec;
   private
      type Rec is new Use_User_Eq;
      C1 : constant Rec := (1, 1);
      C2 : constant Rec := (1, 2);
   end Private_Types;
   use Private_Types;
begin
   pragma Assert (C1 /= C2); --@ASSERT:FAIL
end Main;
