------------------------------------------------------------------------------
--  These are test VCs which exercise private types.
------------------------------------------------------------------------------

package Complex
is
   type Unsigned_Byte is range 0..255;

   type T is private;

   function Create (Real_Part : in Integer;
                    Imag_Part : in Integer)
                   return T;

private
   type T is record
      R : Integer;
      I : Integer;
   end record;
end Complex;
