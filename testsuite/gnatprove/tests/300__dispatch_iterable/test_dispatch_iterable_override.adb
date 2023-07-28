procedure Test_Dispatch_Iterable_Override with SPARK_Mode is

   package Nested is
      type Root is tagged record
         F1, F2, F3, F4 : Integer;
      end record
        with Iterable =>
          (First       => First,
           Next        => Next,
           Has_Element => Has_Element,
           Element     => Element);

      type Cursor is new Positive;

      function First (Dummy : Root) return Cursor is (1);

      function Next (Dummy : Root; C : Cursor) return Cursor is (if C in 1 .. 4 then C + 1 else C);

      function Has_Element (Dummy : Root; C : Cursor) return Boolean is (C in 1 .. 4);

      function Element (R : Root; C : Cursor) return Integer
        with Pre'Class => Has_Element (R, C);

      function Element (R : Root; C : Cursor) return Integer is
        (case C is
            when 1      => R.F1,
            when 2      => R.F2,
            when 3      => R.F3,
            when 4      => R.F4,
            when others => raise Program_Error);

      type Child is new Root with record
         F5 : Integer;
      end record
        with Iterable =>
          (First       => First,
           Next        => Next,
           Has_Element => Has_Element,
           Element     => Element);

      function Has_Element (Dummy : Child; C : Cursor) return Boolean is (C in 1 .. 5);

      function Next (Dummy : Child; C : Cursor) return Cursor is (if C in 1 .. 5 then C + 1 else C);

      function Element (R : Child; C : Cursor) return Integer;

      function Element (R : Child; C : Cursor) return Integer is
        (case C is
            when 1 .. 4 => Element (Root (R), C),
            when 5      => R.F5,
            when others => raise Program_Error);
   end Nested;

   use Nested;

   R : Root := (1, 2, 3, 4);
   C : Child := (1, 2, 3, 4, 5);
begin
   pragma Assert (for all E of R => E <= 4); --@ASSERT:PASS
   --  The Iterable aspect is redefined on Child
   --  pragma Assert (for some E of C => E > 4); --ASSERT:PASS
   --  The assert is commented for now because it crashes flow analysis.
   --  When this is fixed, do not forget to reenable the marker by adding
   --  the missing @.
end Test_Dispatch_Iterable_Override;
