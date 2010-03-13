package body Cursor_Location is

   function Change_Side (Side : Location) return Location is
      pragma Postcondition ((Side = Left and Change_Side'Result = Right) or
                            (Side = Right and Change_Side'Result = Left));
      Result : Location;
   begin
      case Side is
         when Left =>
            Result := Right;
         when Right =>
            Result := Left;
      end case;
      return Result;
   end Change_Side;

   procedure Selection
     (Current      : in out Extended_Location;
      Request      : in Location_Property;
      DU_Available : in Location_Property)
   is
      function Fulfill_Condition (Side : Location) return Boolean is
         pragma Postcondition (DU_Available (Side) and
                               (Request (Side) or
                                not DU_Available (Change_Side (Side))));
         Other_Side : Location;
      begin
         Other_Side := Change_Side (Side);
         return DU_Available (Side) and then
                (Request (Side) or else not DU_Available (Other_Side));
      end Fulfill_Condition;

      function None_Available return Boolean is
         pragma Postcondition (not DU_Available (Left) and
                               not DU_Available (Right));
      begin
         return not DU_Available (Left) and then not DU_Available (Right);
      end None_Available;
   begin
      if Fulfill_Condition (Left) then
         Current := Left;
      elsif Fulfill_Condition (Right) then
         Current := Right;
      elsif None_Available then
         Current := Nil;
      end if;
   end Selection;

end Cursor_Location;
