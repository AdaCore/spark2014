package body Dic_Not_Spark is

   function Add (X : Bad1; Y : in out Natural) return Boolean is
      XX : constant Natural := Natural (X);
   begin
      if Natural'Last - XX >= Y then
         Y := XX + Y;
         return True;
      else
         return False;
      end if;
   end Add;

   package body With_SPARK_Mode with SPARK_Mode => Off is

      function Add (X : Bad2; Y : in out Natural) return Boolean is
         XX : constant Natural := Natural (X);
      begin
         if Natural'Last - XX >= Y then
            Y := XX + Y;
            return True;
         else
            return False;
         end if;
      end Add;
   end With_SPARK_Mode;
end Dic_Not_Spark;
