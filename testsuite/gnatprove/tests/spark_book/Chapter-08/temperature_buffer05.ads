with Data_Types;
--# inherit Data_Types;
package Temperature_Buffer05
  --# own Contents;
is
   type Temperature_Record is
      record
         Time_Stamp : Data_Types.Time_Type;
         Value      : Data_Types.Temperature_Type;
      end record;

   -- Adds a new item to the buffer.
   procedure Put (Item : in Temperature_Record);
   --# global in out Contents;
   --# derives Contents from Contents, Item;

   -- Returns True if buffer is not empty.
   function Has_More return Boolean;
   --# global in Contents;

   -- Retrieves the oldest item from the buffer.
   procedure Get (Item : out Temperature_Record);
   --# global in out Contents;
   --# derives Contents from Contents &
   --#         Item     from Contents;
   --# pre Has_More (Contents);

   -- Initializes the buffer.
   procedure Clear;
   --# global out Contents;
   --# derives Contents from ;

end Temperature_Buffer05;
