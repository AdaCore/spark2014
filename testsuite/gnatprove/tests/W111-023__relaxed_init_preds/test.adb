procedure Test with SPARK_Mode is

   type My_Int is new Integer with
     Relaxed_Initialization,
     Predicate => Integer (My_Int) < Integer'Last
     and Integer (My_Int) + 1 < Integer'Last; -- @OVERFLOW_CHECK:FAIL

   package N is

      type My_Priv is private with
        Annotate => (GNATprove, Ownership, "Needs_Reclamation"),
        Relaxed_Initialization;

      function To_Int (X : My_Priv) return Integer with
        Annotate => (GNATprove, Always_Return);

      subtype S is My_Priv with
        Predicate => To_Int (S) < Integer'Last
        and To_Int (S) + 1 < Integer'Last; -- @OVERFLOW_CHECK:FAIL

   private
      pragma SPARK_Mode (Off);
      type My_Priv is new Integer;

      function To_Int (X : My_Priv) return Integer is (Integer (X));
   end N;

   type My_Rec1 is record
      F : Integer;
   end record with
     Relaxed_Initialization,
     Predicate => F'Initialized
     and then
       (F < Integer'Last
        and F + 1 < Integer'Last); -- @OVERFLOW_CHECK:FAIL

   type My_Rec2 is record
      F : Integer;
   end record with
     Relaxed_Initialization,
     Predicate => F'Initialized
     and F < Integer'Last; -- @INIT_BY_PROOF:FAIL

begin
   null;
end;
