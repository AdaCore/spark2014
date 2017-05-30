with Put_Line;

package body P is

   procedure Dummy with SPARK_Mode => Off is
   begin
      pragma Debug (Put_Line);
   end;

end;
