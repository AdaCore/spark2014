package body R is
   package body Outer is
      procedure P (X : in out Integer) is
      begin
         if X /= 0 then
            X := 0;
         end if;
      end;
   end;
end;
