with Factorial; use Factorial;
with Ada.Text_IO; use Ada.Text_IO;

package body Run
with SPARK_Mode => Off
is

   procedure Factorial (X : in Integer)
   is
   begin
      Put_Line (Integer'Image (X) & "! = " & Integer'Image (Fact (X => X)));
   end Factorial;

   procedure Run is
   begin
      for I in 1 .. 12 loop
         Factorial (X => I);
      end loop;
   end Run;

end Run;
