procedure Repro with SPARK_Mode is
   type R (D : Boolean := False) is null record;

   function F return R is
   begin
      for I in 1 .. 2 loop
         null;
      end loop;

      return X : R (True);
   end F;
begin
   null;
end Repro;
