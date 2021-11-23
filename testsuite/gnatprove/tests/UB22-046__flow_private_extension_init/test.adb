procedure Test with SPARK_Mode is

   type Root is tagged record
      A : Integer;
   end record;

   package Nested is
      type Child is new Root with private;
   private
      pragma SPARK_Mode (Off);
      type Child is new Root with record
         B : Integer;
      end record;
   end Nested;
   use Nested;

   type Grand_Child is new Child with record
      C : Integer;
   end record;

   function Foo (C : Grand_Child) return Boolean is (C.A = 0);
   G : Grand_Child;
begin
   G.A := 1;
   G.C := 2;
   if Foo (G) then --  Here we read G (including its private part) but it is not fully initialized
      null;
   end if;
end Test;
