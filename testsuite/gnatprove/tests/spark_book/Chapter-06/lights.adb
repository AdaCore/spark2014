pragma SPARK_Mode(On);
package body Lights is

   function Next_Color (Current_Color : in Color_Type) return Color_Type is
      Result : Color_Type;
   begin
      case Current_Color is
         when Red =>
            Result := Green;
         when Yellow =>
            Result := Red;
         when Green =>
            Result := Yellow;
      end case;
      return Result;
   end Next_Color;

end Lights;
