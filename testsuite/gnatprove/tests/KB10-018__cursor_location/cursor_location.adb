package body Cursor_Location is

   function Fulfill_Condition
     (Side         : Location;
      Request      : Location_Property;
      DU_Available : Location_Property) return Boolean
   is
      Other_Side : Location;
   begin
      Other_Side := Change_Side (Side);
      return DU_Available (Side) and then
             (Request (Side) or else not DU_Available (Other_Side));
   end Fulfill_Condition;

   function None_Available (DU_Available : Location_Property) return Boolean is
      Pragma Postcondition
         (not DU_Available (Left) and not DU_Available (Right));
   begin
      return not DU_Available (Left) and then not DU_Available (Right);
   end None_Available;

   procedure Selection
     (Current      : in out Extended_Location;
      Request      : in Location_Property;
      DU_Available : in Location_Property)
   is
   begin
      if Fulfill_Condition (Left, Request, DU_Available) then
         Current := Left;
      elsif Fulfill_Condition (Right, Request, DU_Available) then
         Current := Right;
      elsif None_Available (DU_Available) then
         Current := Nil;
      end if;
   end Selection;

end Cursor_Location;
