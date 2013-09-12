package body Rename_Deref is
   pragma SPARK_Mode (Off);
   X : access Integer := new Integer;

   Deref : Integer renames X.all;

   procedure Set is
   begin
      Deref := 0;
   end Set;

   function Get return Integer is
   begin
      return Deref;
   end Get;

   procedure Check is
      Old : Integer := Get;
   begin
      Set;
      pragma Assert (Old = Get);
   end Check;

end;
