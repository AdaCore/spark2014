generic
   type Element_Type is private;

package Lili is
   type Cursor is private;
   function Next (Position : Cursor) return Cursor;
private
   type Cursor is
      record
         Container : Integer;
      end record;

end Lili;
