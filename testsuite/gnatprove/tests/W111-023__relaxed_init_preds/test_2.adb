procedure Test_2 with SPARK_Mode is

   type My_Int is new Integer with
     Relaxed_Initialization,
     Predicate => Integer (My_Int) < Integer'Last;

   subtype S_Int is My_Int with
     Predicate => Integer (S_Int) + 1 < Integer'Last; -- @OVERFLOW_CHECK:PASS

   type My_Rec is record
      F : Integer;
   end record with
     Relaxed_Initialization,
     Predicate => F'Initialized
     and then F < Integer'Last;

   subtype S_Rec is My_Rec with
     Predicate => S_Rec.F + 1 < Integer'Last; -- @OVERFLOW_CHECK:PASS

begin
   null;
end;
