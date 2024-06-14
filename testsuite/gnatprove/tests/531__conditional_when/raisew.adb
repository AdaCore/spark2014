procedure Raisew is
   procedure Idk (Param : Boolean) is
   begin
      raise Program_Error when Param;
      raise Program_Error with "Error!" when Param;
   end;
begin
   null;
end;
