package body Complex
is

   function Create (Real_Part : in Integer;
                    Imag_Part : in Integer)
                   return T
   is
   begin
      return T'(R => Real_Part,
                I => Imag_Part);
   end Create;

end Complex;
