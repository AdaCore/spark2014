package body P is

   function Zero return Integer is (0);

   task body TT is
   begin
      loop
         null;
      end loop;
   end;

   T : TT (Zero); -- @RANGE_CHECK:FAIL

end;
