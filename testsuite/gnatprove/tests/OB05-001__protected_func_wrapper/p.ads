package P is

   protected PO is
      function Dummy return Boolean;
   private
      X : Boolean := False;
   end;

   function Wrapper return Boolean;

--   protected P2 is
--   private
--      Y : Boolean := Wrapper;
--   end;

end;
