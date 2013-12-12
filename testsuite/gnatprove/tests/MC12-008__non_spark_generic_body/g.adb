with Ada.Text_IO;
package body G
--  Aspect here currently illegal. Why?
--  with SPARK_Mode => Off
is
   procedure Op (A : in out T)
   is
   begin
      A := A + 1;

      --  Something not legal SPARK here should be OK,
      --  since this whole package is SPARK_Mode => Off
      if A = 1 then
         goto The_End;
      end if;
      
      Ada.Text_IO.Put_Line ("Final A is " & A'Img);
      
      <<The_End>> null;
   end Op;
end G;

