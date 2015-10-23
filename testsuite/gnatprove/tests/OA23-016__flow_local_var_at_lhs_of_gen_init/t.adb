package body T is
   procedure Set_V is
   begin
      V := 10;
   end Set_V;

   procedure Edit_V is
   begin
      V := V + 1;
   end Edit_V;

   procedure Do_Nothing is
   begin
      null;
   end Do_Nothing;

begin
   Set_V;
   Edit_V;
   Do_Nothing;
end T;
