procedure C390010 is
   -- define a discriminated tagged type, and a constrained subtype of
   -- that type:

   type Discr_Tag_Record (Disc : Boolean) is tagged record
      FieldA : Character := 'A';
      case Disc is
         when True =>
            FieldB : Character := 'B';
         when False =>
            FieldC : Character := 'C';
      end case;
   end record;

   -- derive a type, "passing through" one discriminant, adding one
   -- discriminant, and a constrained subtype of THAT type:

   type Derived_Record (Disc1, Disc2 : Boolean)
   is new Discr_Tag_Record (Disc1) with record
      FieldD : Character := 'D';
      case Disc2 is
         when True =>
            FieldE : Character := 'E';
         when False =>
            FieldF : Character := 'F';
      end case;
   end record;

   type Parent_Class_Access is access all Discr_Tag_Record'Class;

   An_Item : Parent_Class_Access;

begin  -- Main test procedure.
   An_Item := new Derived_Record (False, False);

end C390010;
