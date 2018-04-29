package Competition with
   SPARK_Mode
is

   subtype Zero_Index is Integer range 0 .. 100;  -- arbitrary

   subtype Index is Zero_Index range 1 .. Zero_Index'Last;

   type List is array (Index range <>) of Integer;

   function Unique (Input : List) return List with
      Post => True;

end Competition;
