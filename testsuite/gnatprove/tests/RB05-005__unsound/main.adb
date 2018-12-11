with Ada.Text_IO;
with Longest_Common_Prefix;

procedure Main is

   Result : Natural;

   procedure Test (Expected, Actual : in Natural) is
   begin
      if Expected = Actual then
         Ada.Text_IO.Put_Line("Pass : " & Actual'Image);
      else
         Ada.Text_IO.Put_Line("Fail : " & Actual'Image & ", Expected : " & Expected'Image);
      end if;
   end Test;

begin
   Longest_Common_Prefix.A := (1, 2, 3, 4, 5, 1, 2, 3, 4, 5, others => 0);
   Test(5, Longest_Common_Prefix.LCP(1, 6));
   Test(0, Longest_Common_Prefix.LCP(1, 4));
   Test(2, Longest_Common_Prefix.LCP(4, 9));
   Test(0, Longest_Common_Prefix.LCP(1, 1000));
   Test(0, Longest_Common_Prefix.LCP(1, 10010));

   Result := Longest_Common_Prefix.LCP (1, 1001);

end Main;
