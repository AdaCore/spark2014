pragma Extensions_Allowed (All_Extensions);

package body Test
with SPARK_Mode
is
   type Rec is record
      A : Integer;
      B : Integer;
   end record;

   R : Rec := (A => 0, B => 0);

   function Pick_A (Value : Rec) return Integer is (Value.A);

   procedure Main (O : out Integer) is
   begin
      <<Init>>
      O := Pick_A (R'At (Init));
   end Main;
end Test;
