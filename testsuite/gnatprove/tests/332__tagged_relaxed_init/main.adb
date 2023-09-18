procedure Main with SPARK_Mode is
   function Rand (I : Integer) return Boolean with
     Import,
     Global => null;

   type R is record
      F, G : Integer;
   end record;

   type RR is new R with Relaxed_Initialization;

   package Nested is
      type Root is tagged record
         F : RR;
      end record;
      type Child is new Root with record
         G : Integer;
      end record;
   end Nested;
   use Nested;

   P1 : Root := (F => RR'(others => 1));
   O  : RR;
   P2 : Root := (F => O);
   P3 : Child := (F => RR'(others => 1), G => 1);
   P4 : Child := (F => O, G => 1);
begin
   if Rand (1) then
      pragma Assert (P1.F'Initialized);
   elsif Rand (2) then
      pragma Assert (P2.F'Initialized); -- ASSERT:FAIL
   elsif Rand (3) then
      pragma Assert (P3.F'Initialized);
   elsif Rand (4) then
      pragma Assert (P4.F'Initialized); -- ASSERT:FAIL
   elsif Rand (5) then
      pragma Assert (Root (P3).F'Initialized);
   else
      pragma Assert (Root (P4).F'Initialized); -- ASSERT:FAIL
   end if;
end Main;
