package body Device
--# own State is        OldX,
--#              in     StatusPort,
--#                 out Register;
-- refinement on to mix of external and ordinary variables
is
  OldX : Integer := 0; -- only component that needs initialization
  StatusPort : Integer;
  -- address clause would be added here
  Register : Integer;
  -- address clause would be added here

  procedure WriteReg (X : in Integer)
  --# global out Register;
  --# derives Register from X;
  is
  begin
    Register := X;
  end WriteReg;

  procedure ReadAck (OK : out Boolean)
  --# global in StatusPort;
  --# derives OK from StatusPort;
  is
    RawValue : Integer;
  begin
    RawValue := StatusPort; -- only assignment allowed here
    OK := RawValue = 16#FFFF_FFFF#;
  end ReadAck;

  procedure Write (X : in Integer)
  --# global in out OldX; 
  --#           out Register; 
  --#        in     StatusPort;
  --# derives OldX,Register from OldX, X &
  --#         null          from StatusPort; 
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
