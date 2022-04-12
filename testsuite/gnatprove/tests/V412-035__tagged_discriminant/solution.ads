package Solution with SPARK_Mode is

   type Instance (Max_Words : Integer) is tagged private;

   procedure Add_Word (This : in out Instance);

private

   type Test is array (Integer range <>) of Integer;

   type Instance (Max_Words : Integer) is tagged record
      Placements : Test (1 .. Max_Words);
   end record;

end Solution;
