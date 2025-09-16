with Interfaces;

package Bar is
   type Good is private;
private
   type Good is new Interfaces.Unsigned_32
   with Annotate => (GNATprove, No_Wrap_Around);

   Last : Good := Good (Interfaces.Unsigned_32'Last);
   Wrap : Good := Last + Last;
end;
