package body P is
   protected body PT is
      procedure Proc is
         A : Boolean with Address => C'Address;
      begin
         A := not A;
      end;
      function F return Boolean is
         A : Boolean with Address => C'Address;
      begin
         A := not A;
         return A;
      end;
   end;
end;
