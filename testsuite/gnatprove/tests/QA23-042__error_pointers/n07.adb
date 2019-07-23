-- Forbidden examples : we do not want this to happen in Spark.
-- Already forbidden : returning pointer to stack

with Ada.Text_IO;
use Ada.Text_IO;

procedure N07 is
   package Data is
      type AI is access Integer;
      function Get_Local_Pointer return access Integer;
   end Data;
   package body Data is

      function Get_Local_Pointer return access Integer is
         XX : AI := new Integer'(1);
         X: access Integer := XX;
      begin
         return X; --ERROR non-local pointer cannot point to local object
      end;

   end Data;
   use Data;
   A : access Integer;
begin
   A := Get_Local_Pointer;

end N07;
