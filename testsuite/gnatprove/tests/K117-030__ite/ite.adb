package body Ite is
   procedure Not_Null (X : in out Integer)
   is
   begin
      if X = 0 then
         X := X + 1;
      else
         null;
      end if;
   end Not_Null;
end Ite;
