procedure Test with SPARK_Mode is
   function Id (X : Integer) return Integer is (X);
   C : constant Integer := Id (5);
   type Bool_Array is array (Integer range 1 .. C) of Boolean with Pack;

   type R (Present : Boolean := False) is record
      G : Bool_Array;
      case Present is
         when True =>
            F : Integer;
         when False => null;
      end case;
   end record;

   X : aliased R := (Present => False, G => (others => True));
   Y : aliased R (False) := (Present => False, G => (others => True));

   procedure P (Y : R) with Pre => not Y.Present is
   begin
      pragma Assert (X'Size = Y'Size); -- @ASSERT:FAIL
   end P;

begin
   pragma Assert (X'Size = R'Object_Size); -- @ASSERT:PASS
   P (Y);
end;
