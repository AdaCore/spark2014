procedure P is
   procedure A (X : Integer) is
   begin
      while X < 42 loop --  detected correctly as stable
         null;
      end loop;
   end A;

   procedure B (X : Integer) is
   begin
      loop
         exit when X < 42; --  stable, but not yet detected
      end loop;
   end B;

   procedure C (X : Integer) is
   begin
      loop
         if X < 42 then
            exit;  --  stable, but not yet detected
         end if;
      end loop;
   end C;

begin
   null;
end P;
