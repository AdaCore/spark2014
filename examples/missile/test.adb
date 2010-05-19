-- Auxiliary to test harness
-- $Id: test.adb,v 1.1.1.1 2004/01/12 19:29:12 adi Exp $
--
-- $Log: test.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.3  2003/02/12 23:17:44  adi
-- Added Comment function
--
-- Revision 1.2  2003/02/11 21:09:25  adi
-- Simplified main test body
--
-- Revision 1.1  2003/02/03 19:59:10  adi
-- Initial revision
--
--
with Ada.Text_Io;
package body Test
 --# own State is Pass_Count, Fail_Count;
is

   Pass_Count, Fail_Count : Integer := 0;

   procedure Align(S : in String)
   is
      L : Natural;
   begin
      Ada.Text_Io.Put(S);
      L := S'Last;
      for I in Natural range (L+1)..40 loop
         Ada.Text_Io.Put(' ');
      end loop;
   end Align;

   procedure Pass(S : in String)
   is begin
      Ada.Text_Io.Put_Line("PASS" & S);
      Pass_Count := Pass_Count + 1;
   end Pass;

   procedure Fail(S : in String)
   is begin
      Ada.Text_Io.Put_Line("    FAIL:" & S);
      Fail_Count := Fail_Count + 1;
   end Fail;

   procedure Section(S : in String)
   is begin
      Ada.Text_Io.Put_Line("---------------------------------");
      Ada.Text_Io.Put_Line(S);
   end Section;

   procedure Comment(S : in String)
   is begin
      Ada.Text_Io.Put_Line(S);
   end Comment;

   procedure Done
   is begin
      Ada.Text_Io.Put_Line("DONE.");
      Ada.Text_Io.Put("  Passes: ");
      Ada.Text_Io.Put_Line(Natural'Image(Pass_Count));
      Ada.Text_Io.Put("  Fails:  ");
      Ada.Text_Io.Put_Line(Natural'Image(Fail_Count));
   end Done;

   function Passes return Natural
   is begin
      return Pass_Count;
   end Passes;

   function Fails return Natural
   is begin
      return Fail_Count;
   end Fails;
end Test;
