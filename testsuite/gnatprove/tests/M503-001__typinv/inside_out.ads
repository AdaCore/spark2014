package Inside_Out with SPARK_Mode is

   type T is private;

   procedure Create (X : out T);  --  @INVARIANT_CHECK:FAIL

   procedure Update (X : in out T);  --  @INVARIANT_CHECK:FAIL

   function Get (X : T) return Integer;

private

   type T is new Integer with  --  @INVARIANT_CHECK_ON_DEFAULT_VALUE:PASS
     Default_Value => 42,
     Type_Invariant => T /= 0;

   procedure Priv_Create (X : out T);

   procedure Priv_Update (X : in out T);

   function Priv_Get (X : T) return Integer;

end Inside_Out;
