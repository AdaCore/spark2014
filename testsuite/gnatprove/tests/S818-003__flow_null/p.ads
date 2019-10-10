package P is

   --  Dummy procedures with different combinations of Global/Depends => null

   procedure Dummy_With_Global
   with Global => null;

   procedure Dummy_With_Depends
   with Depends => null;

   procedure Dummy_With_Global_And_Depends
   with Global => null, Depends => null;

   --  Same as above, but with extra Import & Convention aspects

   procedure Dummy_With_Global_And_Imported
   with Global => null, Import => True, Convention => C;

   procedure Dummy_With_Depends_And_Imported
   with Depends => null, Import => True, Convention => C;

   procedure Dummy_With_Global_And_Depends_And_Imported
   with Global => null, Depends => null, Import => True, Convention => C;
end;
