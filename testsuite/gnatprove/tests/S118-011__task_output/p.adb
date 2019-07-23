package body P is
   task body T is
      procedure Dummy with Pre => True, Global => (Output => T) is begin null; end;
   begin
      loop
         Dummy;
      end loop;
   end;
end;
