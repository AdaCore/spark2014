package Int_Arith is

   subtype Index is Integer range 0 .. 1_000_000;
   Max_Value : constant := 1_000;
   subtype Value is Integer range 0 .. Max_Value;

   type Base_Data is array (Index range <>) of Value with
     Relaxed_Initialization;

   subtype Data is Base_Data with
     Predicate => Data'First = 1 and Data'Last >= 0;

   function Sum (A : Data; Up_To : Index) return Integer is
     (if Up_To = 0 then 0 else A(Up_To) + Sum (A, Up_To - 1))
   with
     Pre  => Up_To <= A'Last
       and then (for all J in 1 .. Up_To => A(J)'Initialized),
     Post => Sum'Result <= Up_To * Max_Value,
     Subprogram_Variant => (Decreases => Up_To);

   procedure Init_SPARK (A : in out Data; S : Natural)
   with
     Pre  => S <= A'Length,
     Post => Sum (A, S) = S;

end Int_Arith;
