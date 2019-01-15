package body Top.Gen.Sub
is
   procedure Update (S : in out State_Type)
   is
   begin
      if S.X > 0 then
         S.X := 0;
      end if;
   end Update;

end Top.Gen.Sub;
