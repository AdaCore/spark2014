package Object is
   type T is abstract tagged private;

   function Has_Stored_Area (Obj : T) return Boolean;

   function Get_Stored_Area (Obj : T) return Natural with
     Pre'Class => Obj.Has_Stored_Area;

   procedure Get_Area (Obj : in out T; Result : out Natural) is abstract with
     Post'Class => Obj.Has_Stored_Area and then
                   Result = Obj.Get_Stored_Area;

   procedure Set_Area (Obj : in out T; Value : Natural) with
     Post'Class => Obj.Has_Stored_Area and then
                   Value = Obj.Get_Stored_Area;

private

   No_Area : constant := -1;
   No_Length : constant := -1;

   type T is abstract tagged record
      Area       : Integer := No_Area;  -- set to -1 if not yet computed
      Max_Width  : Integer := No_Length;
      Max_Height : Integer := No_Length;
   end record;

   function Has_Stored_Area (Obj : T) return Boolean is (Obj.Area in Natural);

   function Get_Stored_Area (Obj : T) return Natural is (Obj.Area);

end Object;
