package body Device
  with SPARK_Mode,
       Refined_State => (State => (OldX,
                                   StatusPort,
                                   Register))
   -- refinement on to mix of external and ordinary variables
is
   type Status_Port_Type is mod 2**32;

   OldX : Integer := 0; -- only component that needs initialization

   StatusPort : Status_Port_Type
     with Volatile,
          Async_Writers;
   -- address clause would be added here

   Register : Integer
     with Volatile,
          Async_Readers;
   -- address clause would be added here

   procedure WriteReg (X : in Integer)
     with Global  => (Output => Register),
          Depends => (Register => X)
   is
   begin
      Register := X;
   end WriteReg;

   procedure ReadAck (OK : out Boolean)
     with Global  => (Input => StatusPort),
          Depends => (OK => StatusPort)
   is
      RawValue : Status_Port_Type;
   begin
      RawValue := StatusPort; -- only assignment allowed here
      OK := RawValue = 16#FFFF_FFFF#;
   end ReadAck;

   procedure Write (X : in Integer)
     with Refined_Global  => (Input  => StatusPort,
                              Output => Register,
                              In_Out => OldX),
          Refined_Depends => ((OldX,
                               Register) => (OldX,
                                             X),
                               null => StatusPort)
   is
      OK : Boolean;
   begin
      if X /= OldX then
         OldX := X;
         WriteReg (X);
         loop
            ReadAck (OK);
            exit when OK;
         end loop;
      end if;
   end Write;
end Device;
