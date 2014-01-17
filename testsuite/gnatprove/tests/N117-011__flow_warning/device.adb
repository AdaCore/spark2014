package body Device
  with SPARK_Mode,
       Refined_State => (State => (OldX,
                                   StatusPort,
                                   Register))
   -- refinement on to mix of external and ordinary variables
is
   type Status_Port_Type is mod 2**32;

   OldX : Integer := 0; -- only component that needs initialization

   pragma Warnings (Off, "pragma * is not yet supported*");
   -- By release 1 these warnings should not be raised;
   -- pending completetion of the implementation of External State.
   -- At the moment initialization is required for volatile variables to avoid
   -- an error, but the error will be downgraded to a suppressible warning for
   -- when referring to a volatile variable.
   -- After release 1 we may consider introducing Read_Only and Write_Only
   -- states.  Neither of these would require initialization.
   StatusPort : Status_Port_Type := 0
     with Volatile,
        Async_Writers;
   -- address clause would be added here

   Register : Integer := 0
     with Volatile,
          Async_Readers;
   -- address clause would be added here
   pragma Warnings (On, "pragma * is not yet supported*");

   procedure WriteReg (X : in Integer)
     with Global  => (Output => Register),
          Depends => (Register => X)
   is
   begin
      Register := X;
   end WriteReg;

   procedure ReadAck (OK : out Boolean)
     with Refined_Global  => (Input => StatusPort),
          Refined_Depends => (OK => StatusPort)
   is
      RawValue : Status_Port_Type;
   begin
      RawValue := StatusPort; -- only assignment allowed here
      OK := RawValue = 16#FFFF_FFFF#;
   end ReadAck;

   function Last_Written return Integer is (OldX)
     with Refined_Global => OldX;

   -- We have not designated StatusPort as having effective reads and so
   -- the wait loop appears to be ineffective.
   pragma Warnings (Off, "Unused*");
   -- We do not have write only variables yet and so it is assumed that the
   -- the value of Register may be read.  For this reason a flow warning is
   -- reported that the value of Register is not assigned a value on all paths.
   -- After release 1 we may consider write only variables and for such
   -- variables this warning would not be generated.
   pragma Warnings (Off, """Register"" might not be written");
   procedure Write (X : in Integer)
     with Refined_Global  => (Input => StatusPort,
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
         pragma Warnings (Off, "statement has no effect");
         loop
            ReadAck (OK);
            exit when OK;
         end loop;
         pragma Warnings (On, "statement has no effect");
      end if;
   end Write;
   pragma Warnings (On, "Unused*");
   pragma Warnings (On, """Register"" might not be written");
end Device;
