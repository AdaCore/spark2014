with Object;
with Rectangle;

package Window is

   Total_Area : Natural := 10_000;

   procedure Draw (Obj : Object.T'Class) with
     Global => (In_Out => Total_Area),
     Pre    => Obj.Has_Stored_Area,
     Post   => Total_Area = Total_Area'Old - Obj.Get_Stored_Area;

   procedure Prepare_To_Draw (Obj : in out Object.T'Class) with
     Global => null,
     Post   => Obj.Has_Stored_Area;

   procedure Draw_Large_Rectangle with
     Pre  => Total_Area > 100,
     Post => Total_Area = Total_Area'Old - 100;

end Window;
