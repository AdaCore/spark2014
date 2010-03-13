package Cursor_Location is

   type Extended_Location is (Nil, Left, Right);
   subtype Location is Extended_Location range Left .. Right;

   type Location_Property is array (Location) of Boolean;

   procedure Selection
     (Current      : in out Extended_Location;
      Request      : in Location_Property;
      DU_Available : in Location_Property);
   pragma Postcondition
     ((if not DU_Available (Left) then Current /= Left) and
     (if not DU_Available (Right) then Current /= Right));

end Cursor_Location;
