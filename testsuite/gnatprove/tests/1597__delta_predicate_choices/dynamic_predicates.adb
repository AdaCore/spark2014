procedure Dynamic_Predicates (Selected : Integer) with
  SPARK_Mode,
  Pre => Selected in 2 | 4
is
   subtype Even is Integer range 1 .. 4
     with Dynamic_Predicate => Even mod 2 = 0;
   subtype Narrow is Even range 2 .. Selected;
   subtype Pick is Even
     with Dynamic_Predicate => Pick = Selected;
   type Vector is array (1 .. 4) of Integer;
   X : constant Vector := [others => 0];
   Y : constant Vector := (X with delta Even => 9);
   Z : constant Vector := (X with delta Narrow => 8);
   W : constant Vector := (X with delta Pick => 7);
   V : constant Vector := (X with delta Even range 2 .. Selected => 6);
begin
   pragma Assert (Y = [0, 9, 0, 9]); -- @ASSERT:PASS
   pragma Assert (Z = [0, 8, 0, (if Selected = 4 then 8 else 0)]); -- @ASSERT:PASS
   pragma Assert (W = [0, (if Selected = 2 then 7 else 0), 0, (if Selected = 4 then 7 else 0)]); -- @ASSERT:PASS
   pragma Assert (V = [0, 6, 0, (if Selected = 4 then 6 else 0)]); -- @ASSERT:PASS
end Dynamic_Predicates;
