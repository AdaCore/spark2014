with Const;

package P with SPARK_Mode is

   type Sector_Coords_Range_T is range 0 .. Const.Length;
   for Sector_Coords_Range_T'Size use 8;
   --# assert Sector_Coords_Range_T'Base is Short_Short_Integer;
   --  ??? and old-SPARK style assumption

   pragma Assert (Short_Short_Integer (Sector_Coords_Range_T'Base'First) = Short_Short_Integer'First and
                  Short_Short_Integer (Sector_Coords_Range_T'Base'Last)  = Short_Short_Integer'Last,
                  "Incorrect base type assertion");
   --  this pragma is statically known to be true,
   --  yet still it causes translation of the entire unit
   --  ??? perhaps to verify the old style assumption

   pragma Assert (False);
   --  a similar but statically false pragma gives a message with "might fail",
   --  while we know it always fails

   procedure Foo with Pre => False;
   --  note: a similar always-false precondition gives an nice "always false" message

end;
