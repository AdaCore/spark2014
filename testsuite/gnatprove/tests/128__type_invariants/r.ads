package R with SPARK_Mode is
   type T is private;

   function F (X : T) return Boolean;
private

   type T is record
      B : Integer;
   end record
     with Type_Invariant => F (T); -- @BOUNDARY_CALL_IN_INVARIANT:CHECK
end R;
