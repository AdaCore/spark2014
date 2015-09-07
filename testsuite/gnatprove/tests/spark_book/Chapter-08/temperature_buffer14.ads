with Data_Types;
package Temperature_Buffer14
  with
    SPARK_Mode => On,
    Abstract_State => Contents
is
   type Temperature_Record is
      record
         Time_Stamp : Data_Types.Time_Type;
         Value      : Data_Types.Temperature_Type;
      end record;

   -- Initializes the buffer.
   procedure Clear
     with
       Global  => (Output => Contents),
       Depends => (Contents => null);

   -- Adds a new item to the buffer.
   procedure Put (Item : in Temperature_Record)
     with
       Global  => (In_Out => Contents),
       Depends => (Contents =>+ Item);

   -- Returns True if buffer is not empty.
   function Has_More return Boolean
     with Global => (Input => Contents);

   -- Retrieves the oldest item from the buffer.
   procedure Get (Item : out Temperature_Record)
     with
       Global  => (In_Out => Contents),
       Depends => (Contents =>+ null, Item => Contents),
       Pre => Has_More;

end Temperature_Buffer14;
