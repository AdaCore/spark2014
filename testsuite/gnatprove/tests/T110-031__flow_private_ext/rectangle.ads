with Object;

package Rectangle with SPARK_Mode is
   type T is new Object.T with private;
   -- The parent type Object.T is initialized by default, but the private
   -- extension is not.

   procedure Set_Width (Rec : in out T; Value : Natural);
   procedure Set_Height (Rec : in out T; Value : Natural);

private
   pragma SPARK_Mode (Off);
   type T is new Object.T with record
      Width  : Natural;  --  no default initialization
      Height : Natural;  --  no default initialization
   end record;

end Rectangle;
