procedure Badconcat with
  SPARK_Mode
is

   type Octet is mod 2**8;
   type Octet_Array is array(Natural range <>) of Octet;

   function Put_Integer_Value(Value : Integer) return Octet_Array with
     Pre => True;

   function Put_Integer_Value(Value : Integer) return Octet_Array is
   begin
      return (0 .. 1 => 0);
   end Put_Integer_Value;

   TST_Info : constant Octet_Array :=
     Put_Integer_Value(0) &
     Put_Integer_Value(0) &
     Put_Integer_Value(0) &
     Put_Integer_Value(0);
begin
   null;
end Badconcat;
