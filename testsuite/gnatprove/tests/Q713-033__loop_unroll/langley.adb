procedure Langley with SPARK_Mode is
   type Integer_32 is new Integer;
   type Ints is array (Integer range 0 .. 9) of Integer_32;

   function Add (X, Y : in Ints) return Ints with
     Pre => (for all i in Ints'Range => X(i) < 2**30 and X(i) > -2**30 and Y(i) < 2**30 and Y(i) > -2**30),
     Post => (for all i in Ints'Range => Add'Result(i) = X(i) + Y(i));

   function Add (X, Y : in Ints) return Ints is
      Sum : Ints;
   begin
      for i in Ints'Range loop
         Sum(i) := X(i) + Y(i);
      end loop;
      return Sum;
   end Add;
begin
   null;
end Langley;
