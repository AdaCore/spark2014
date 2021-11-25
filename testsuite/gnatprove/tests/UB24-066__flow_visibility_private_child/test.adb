procedure Test with SPARK_Mode is

   type Root is tagged record
      A : Integer;
   end record;

   type Child is new Root with record
      B : Integer;
   end record;

   package Nested is
      type Grand_Child is new Root with private;
   private
      type Grand_Child is new Child with record --  We derive privately from Child, which is legal
         C : Integer;
      end record;
   end Nested;
   use Nested;

   type Grand_Grand_Child is new Grand_Child with record
      D : Integer;
   end record;

   function Foo (C : Grand_Grand_Child) return Boolean is (C.A = 0);
   G : Grand_Grand_Child;
begin
   G.A := 1;
   --  G.B := 1;   --  Uncommenting this line makes the code not compile, because B is not a component of G
   G.D := 3;
   if Foo (G) then --  Here we complain about G.B not being initialized
      null;
   end if;
end Test;
