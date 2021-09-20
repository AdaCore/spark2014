procedure Main with SPARK_Mode is
   type Element is mod 2**8;
   type Element_Array is array (Positive range <>) of Element;
   type Access_Elements is access Element_Array;
   type Channel_Endpoint is tagged record
      Data : Access_Elements;
   end record;
   type Channel_OK is new Channel_Endpoint with record
      V : Element;
   end record;
   type Channel_Bad is new Channel_Endpoint with record
      Data2 : Access_Elements;
   end record;

   subtype S_Ok is Channel_OK with Predicate => S_Ok.V /= 0;
begin
   null;
end;
