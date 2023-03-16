procedure Empty_String with Spark_Mode is

   function Id (I : Integer) return Integer is (I);

   subtype STA is INTEGER range 4 .. 7;
   type TA is array(STA range 5 .. 6,
                    STA range 6 .. Id(4)) of CHARACTER;

   A : TA := (5 .. 6 => "");

begin

   if (6 .. Id(8) => "") = A then
      pragma Assert (False);
   end if;

end Empty_String;
