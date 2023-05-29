package body Exc_Prot with SPARK_Mode is

   protected body Counter is
      function Get return Natural is (X);

      procedure Init is
      begin
        X := 0;
      end Init;

      procedure Incr is
      begin
         if X = Integer'Last then
            raise Overflow;
         else
            X := X + 1;
         end if;
      end Incr;

      procedure Incr_Twice is
      begin
         Incr;
         Incr;
      end Incr_Twice;
   end Counter;

end;
