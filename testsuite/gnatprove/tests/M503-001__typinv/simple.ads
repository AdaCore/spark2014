package Simple with SPARK_Mode is

   type T is private;

   procedure Create (X : out T);  --  @INVARIANT_CHECK:PASS

   procedure Update (X : in out T);  --  @INVARIANT_CHECK:PASS

   function Get (X : T) return Integer;

private

   type T is new Integer with
     Default_Value => 42,
     Type_Invariant => T /= 0;

end Simple;
