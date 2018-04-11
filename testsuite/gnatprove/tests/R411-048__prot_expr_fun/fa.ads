package FA is

   protected type PT is
      function F return Integer;
   private
      X : Integer := 0;
      Y : Integer;
   end PT;

end;
