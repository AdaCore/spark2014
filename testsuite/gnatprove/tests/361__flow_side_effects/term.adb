function Term (X : in out Boolean) return Boolean is
begin
   loop
      X := not X;
      exit when X and not X;
   end loop;
   return X;
end;
