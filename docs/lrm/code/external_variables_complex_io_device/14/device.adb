package body Device
  with Refined_State => (State => (OldX,
                                   StatusPort,
                                   Register))
   -- refinement on to mix of external and ordinary variables
is
   OldX : Integer := 0; -- only component that needs initialization
   StatusPort : Integer
     with Volatile, Input_Only;
   -- address clause would be added here

   Register : Integer
     with Volatile, Output_Only;
   -- address clause would be added here

   procedure WriteReg (X : in Integer)
     with Refined_Global  => (Output => Register),
          Refined_Depends => (Register => X)
   is
   begin
      Register := X;
   end WriteReg;

   procedure ReadAck (OK : out Boolean)
     with Refined_Global  => (Input => StatusPort),
          Refined_Depends => (OK => StatusPort)
   is
      RawValue : Integer;
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
