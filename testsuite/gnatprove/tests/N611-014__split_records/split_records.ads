package Split_Records with SPARK_Mode is

   type Record_With_Mutable_Discrs (Present : Boolean := False) is record
      case Present is
         when True =>
            Field : Natural;
         when False => null;
      end case;
   end record;

   type Mutable_Holder is record
      Content : Record_With_Mutable_Discrs;
   end record;

   type Holder (Present : Boolean) is record
      Content : Record_With_Mutable_Discrs (Present);
   end record;

   type Mutable_Array is array (Positive range <>) of
     Record_With_Mutable_Discrs;

   procedure Update_Field_If_Possible
     (R : in out Record_With_Mutable_Discrs; New_Field : Natural) with
     Post => (if R.Present then R.Field = New_Field);
--       and then (if not R'Constrained then R.Present);

   procedure Test;
end Split_Records;
