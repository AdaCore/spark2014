with Interfaces;
package Serial_Port
   with
      SPARK_Mode     => On,
      Abstract_State => (Port_State, (Data_State with External)),
      Initializes    => Port_State
is
   -- Types for configuring serial parameters.
   type Baud_Type      is (B2400, B4800, B9600, B19200);
   type Parity_Type    is (None, Even, Odd);
   type Data_Size_Type is (Seven, Eight);
   type Stop_Type      is (One, Two);

   -- Type for serial port data
   type Byte is new Interfaces.Unsigned_8;

   -- Type used to convey error codes.
   type Status_Type is (Success, Open_Failure, IO_Failure);

   -- Returns Open_Failure if port is already open or if the open fails.
   procedure Open (Baud      : in  Baud_Type;
                   Parity    : in  Parity_Type;
                   Data_Size : in  Data_Size_Type;
                   Stop      : in  Stop_Type;
                   Status    : out Status_Type)
      with
         Global  => (In_Out => Port_State),
         Depends => ((Port_State, Status) =>
                     (Port_State, Baud, Parity, Data_Size, Stop));

   -- Returns IO_Failure if port is not open or if the underlying I/O fails.
   procedure Read (Item   : out Byte;
                   Status : out Status_Type)
      with
         Global  => (Input => (Port_State, Data_State)),
         Depends => (Item  => (Port_State, Data_State), Status => Port_State);

   -- Returns IO_Failure if port is not open or if the underlying I/O fails.
   procedure Write (Item   : in  Byte;
                    Status : out Status_Type)
      with
         Global  => (Input => Port_State, Output => Data_State),
         Depends => (Data_State => (Port_State, Item), Status => Port_State);

   -- Has no effect if port is not open. Returns no failure indication.
   procedure Close
      with
         Global  => (In_Out => Port_State),
         Depends => (Port_State => Port_State);
end Serial_Port;
