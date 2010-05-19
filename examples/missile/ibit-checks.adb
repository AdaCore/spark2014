-- IBIT checking
--
-- $Log: ibit-checks.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/10 20:04:51  adi
-- Initial revision
--
--
package body IBIT.checks is

   procedure Phase(S : in String;
                   Expected, Actual : in Ibit.Phase)
   is
   begin
      Test.Align(S);
      if Expected = Actual then
         Test.Pass(" ");
      else
         Test.Fail(Ibit.Phase'Image(Actual));
      end if;
   end Phase;

end IBIT.checks;

