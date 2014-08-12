procedure Foo (N : Natural) is

   package Nested
   --  computed global should probably not involve N
   is
      type Glob is private;
      type Wrong_Glob is private;

      function Glob_Ok (X : Glob) return Boolean;
      --  computed global should invlove N

      function Wrong_Glob_Ok (X : Wrong_Glob) return Boolean;
      --  computed glboal should not involve N
   private
      type Glob is record
         F : Natural := N;
      end record;

      type Wrong_Glob is record
         F : Natural;
      end record;

      function Glob_Ok (X : Glob) return Boolean is (X.F = 5);
      function Wrong_Glob_Ok (X : Wrong_Glob) return Boolean is (X.F = 5);
   end Nested;
   use Nested;

   G1 : Glob;
begin
   pragma Assert (Glob_Ok (G1));
end Foo;
