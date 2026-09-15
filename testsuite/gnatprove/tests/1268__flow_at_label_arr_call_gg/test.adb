pragma Extensions_Allowed (All_Extensions);

package body Test
with SPARK_Mode
is
   type Arr is array (1 .. 2) of Integer;

   A : Arr := (0, 0);

   function First (Value : Arr) return Integer is (Value (1));

   procedure Main (O : out Integer) is
   begin
      <<Capture>>
      O := First (A'At (Capture));
   end Main;
end Test;
