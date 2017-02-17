package body Flowsubp with
  SPARK_Mode
is

   procedure P (X : out Integer; B : Boolean) is

      procedure Local (X : out Integer; B : Boolean) is
      begin
         if B then
            X := 1;
         end if;
      end Local;
   begin
      Local (X, B);
   end P;

end Flowsubp;
