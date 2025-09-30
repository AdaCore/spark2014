pragma Extensions_Allowed (All_Extensions);

procedure Test12 (Y : out Integer) is
begin
   Y := 1;
   raise Program_Error;
exception
   when Program_Error =>
      Y := 2;
finally
   Y := 3;
end;
