generic
   Size : Positive;

package Test
is

   subtype Range_Type is Natural range 0 .. Size;

   type Elem_Type (Kind : Boolean := False)
   is private;

private

   type Elem_Type
     (Kind : Boolean := False)
   is record
      case Kind is
         when True =>
            Pos : Integer;
         when others =>
            null;
      end case;
   end record;

end Test;
