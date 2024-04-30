procedure Retw is
   CONST : constant Boolean := True;
   function X (Idk : Boolean) return Boolean is
   begin
      return false when Idk;
      return True;
   end;
begin
   null;
end;
