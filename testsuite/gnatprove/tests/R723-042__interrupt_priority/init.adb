with Logger;

procedure Init is
   --  Init is a main subprogram of a partition, whose priority defaults to
   --  System.Default_Priority.
begin
   Logger.log;
   --  This ultimately calls a protected operation in an object, that is only
   --  visible by the GG machinery; this object has an interrupt, so it gets an
   --  implicit priority of System.Interrupt_Priority'First (but it could be
   --  other priorities too).
   --
   --  To emit the VC for the ceiling priority protocol check we need to pull
   --  both System.Default_Priority and System.Interrupt_Priority when marking
   --  this subprogram body.
end;
