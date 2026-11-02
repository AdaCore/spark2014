procedure Nested_Validity with SPARK_Mode is
   type Inner (D : Integer) is record
      Value : Integer;
   end record;
   type Items is array (1 .. 2) of Inner (0);
   type Outer is record
      Data  : Items;
      Item  : Inner (0);
      Small : Natural;
   end record;
   X : Outer :=
     (Data  => (others => (D => 0, Value => 0)),
      Item  => (D => 0, Value => 0),
      Small => 0)
     with Potentially_Invalid;
begin
   pragma Assert (X.Data (1).D = 0);
   pragma Assert (X.Data (1).Value'Valid);
   pragma Assert (X.Data (2).Value = 0);
   pragma Assert (X.Item.D = 0);
   pragma Assert (X.Item.Value'Valid);
   pragma Assert (X.Item.Value = 0);
   pragma Assert (X.Small'Valid);
   pragma Assert (X.Small = 0);
   pragma Assert (X.Small = 1); --@ASSERT:FAIL
end Nested_Validity;
