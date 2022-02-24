with Types; use Types;

procedure Bar (X : in out Ptr)
is
   Z : Ptr := X;
begin
   loop
      if Z.all > 10 then
         X := Z;
         exit;
      end if;

      Z.all := Z.all * 2;
   end loop;
end Bar;
