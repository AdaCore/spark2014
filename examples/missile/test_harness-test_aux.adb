-- Test the auxiliary functions
-- $Log: test_harness-test_aux.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/08/20 20:34:57  adi
-- Added randomness test
--
-- Revision 1.1  2003/08/12 18:21:03  adi
-- Initial revision
--
--
with Drag, random;
with ada.text_io;
separate(Test_Harness)
procedure Test_Aux is
   procedure Rand_Test(S : in Random.value) is separate;
begin
   -- test with a seed
   Rand_Test(45);
   drag.testpoint;
end test_aux;
