package Cursor_Location is

   type Extended_Location is (Nil, Left, Right);
   subtype Location is Extended_Location range Left .. Right;

   type Location_Property is array (Location) of Boolean;

   function Change_Side (Side : Location) return Location is
      (case Side is
         when Left => Right,
         when Right => Left);

   function Fulfill_Condition
     (Side         : Location;
      Request      : Location_Property;
      DU_Available : Location_Property) return Boolean
      with Post =>
        (DU_Available (Side) and
         (Request (Side) or
          not DU_Available (Change_Side (Side))));

   procedure Selection
     (Current      : in out Extended_Location;
      Request      : in Location_Property;
      DU_Available : in Location_Property)
      with Post =>
        ((if not DU_Available (Left) then Current /= Left) and
        (if not DU_Available (Right) then Current /= Right));

end Cursor_Location;
