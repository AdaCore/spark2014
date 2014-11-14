procedure Minimal
is
   type Record_With_Mutable_Discrs (Present : Boolean := False) is record
      case Present is
         when True =>
            Field : Natural;
         when False => null;
      end case;
   end record;
   C2 : Record_With_Mutable_Discrs := (Present => False);
begin
   pragma Assert (C2.Present); --@ASSERT:FAIL
end Minimal;
