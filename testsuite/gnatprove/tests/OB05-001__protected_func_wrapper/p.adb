package body P is

   protected body PO is
      function Dummy return Boolean is (X);
   end;

   function Wrapper return Boolean is (PO.Dummy);

--   protected body P2 is
--   end;

end;
