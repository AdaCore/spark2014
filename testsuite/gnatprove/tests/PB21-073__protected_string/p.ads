package P is

   protected type PT (X : Integer) is
      function Get return String;
   private
      S : String (1 .. X) := (others => ' ');
   end;

   PO : PT (3);

end;
