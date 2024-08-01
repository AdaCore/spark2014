package body P is
   function Set return Boolean is
   begin
      X := True;
      return True;
   end;

   procedure Proc1 is
      Y : Boolean;
   begin
      Y := Set;
   end;

   procedure Proc2 (C : Boolean) is
      Y : Boolean;
   begin
      if C then
         Y := Set;
      end if;
   end;
end;
