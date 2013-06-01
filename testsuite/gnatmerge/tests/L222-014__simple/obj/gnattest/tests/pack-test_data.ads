with AUnit.Test_Fixtures;

package Pack.Test_Data is

   type Test is new AUnit.Test_Fixtures.Test_Fixture
   with null record;

   procedure Set_Up (Gnattest_T : in out Test);
   procedure Tear_Down (Gnattest_T : in out Test);

end Pack.Test_Data;
