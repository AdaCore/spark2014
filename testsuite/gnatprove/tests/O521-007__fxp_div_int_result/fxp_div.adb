procedure Fxp_div is

   --  prelude

   Time_Span_First : constant Duration := Duration'First;

   Time_Span_Last  : constant Duration := Duration'Last;

   Time_Span_Zero  : constant Duration := 0.0;

   Time_Span_Unit  : constant Duration := 10#1.0#E-9;

   type Duration_Rep is range -(2 ** 63) .. +((2 ** 63 - 1)) with Ghost;
   for Duration_Rep'Size use 64;

   --  precondition with non-linear arithmetic expression;
   --  may need an interative theorem prover

   function multiply  (Left : Duration; Right : Integer) return Duration with
     Pre =>
       (Right > 0 and then Left > Time_Span_Zero and then
          Duration_Rep (Left / Duration (Duration'Small)) <=
            Duration_Rep (Time_Span_Last / Duration'Small) /
            Duration_Rep (Right));

   --  Note that Constraint_Error may be propagated

   function multiply (Left : Duration; Right : Integer) return Duration is
      pragma Unsuppress (Overflow_Check);
   begin
      return Left * Right;
   end multiply;

   X : constant Duration := multiply (Time_Span_Last, 1);

begin
   null;
end Fxp_div;
