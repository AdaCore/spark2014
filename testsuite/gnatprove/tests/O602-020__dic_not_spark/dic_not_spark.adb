package body Dic_Not_Spark is

   Global : Natural;

   function Add (X : Bad1; Y : Natural) return Boolean is
      XX : constant Natural := Natural (X);
   begin
      if Natural'Last - XX >= Y then
         Global := XX + Y;
         return True;
      else
         return False;
      end if;
   end Add;

   package body With_SPARK_Mode with SPARK_Mode => Off is

      function Add (X : Bad2; Y : Natural) return Boolean is
         XX : constant Natural := Natural (X);
      begin
         if Natural'Last - XX >= Y then
            Global := XX + Y;
            return True;
         else
            return False;
         end if;
      end Add;
   end With_SPARK_Mode;
end Dic_Not_Spark;
