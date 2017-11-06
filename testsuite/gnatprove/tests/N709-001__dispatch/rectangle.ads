with Object;

package Rectangle is pragma Elaborate_Body;
   type T is new Object.T with private;

   procedure Get_Area (Rec : in out T; Result : out Natural);

   procedure Set_Width (Rec : in out T; Value : Natural);
   procedure Set_Height (Rec : in out T; Value : Natural);

private

   type T is new Object.T with record
      Width  : Natural;
      Height : Natural;
   end record;

end Rectangle;
