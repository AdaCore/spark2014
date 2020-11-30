with Parent.Child;    -- Private generic child package.

package body Parent is

   -----------------------------------------------------
   -- Parent's body depends on private generic child. --
   -----------------------------------------------------

   -- Instantiate the private child.

   package Complex_Ops is new Child;
   use Complex_Ops;                    -- All user-defined operators
                                       -- directly visible.

   function "*" (Factor : Int_Type;
                 C      : Complex_Type) return Complex_Type is
      Result : Complex_Type := Zero;

   begin
      for I in 1 .. abs (Factor) loop
         Result := Result + C;         -- Private generic child "+".
      end loop;

      if Factor < 0 then
         Result := - Result;           -- Private generic child "-".
      end if;

      return Result;
   end "*";

   function Real_Part (Complex_No : Complex_Type) return Int_Type is
   begin
      return (Complex_No.Real);
   end Real_Part;

   function Imag_Part (Complex_No : Complex_Type) return Int_Type is
   begin
      return (Complex_No.Imag);
   end Imag_Part;

   function Complex (Real, Imag : Int_Type) return Complex_Type is
   begin
      return (Real, Imag);
   end Complex;

end Parent;
