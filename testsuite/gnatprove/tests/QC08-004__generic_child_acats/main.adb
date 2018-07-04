with Parent;                        -- Complex number abstraction.
with Report;

procedure Main is

   type My_Integer is range -100 .. 100;

-- Declare instance of the generic complex package for one particular
-- integer type.

   package My_Complex_Pkg is new
     Parent (Int_Type => My_Integer);

   use My_Complex_Pkg;                 -- All user-defined operators
                                       -- directly visible.

   Complex_One, Complex_Two : Complex_Type;

   My_Literal               : My_Integer := -3;

begin

   Report.Test ("CA11021", "Check that body of the generic parent package " &
                "can depend on its private generic child");

   Complex_One := Complex (11, 6);

   Complex_Two := 5 * Complex_One;

   if Real_Part (Complex_Two) /= 55
     and Imag_Part (Complex_Two) /= 30
        then
           Report.Failed ("Incorrect results from complex operation");
   end if;

   Complex_One := Complex (-4, 7);

   Complex_Two := My_Literal * Complex_One;

   if Real_Part (Complex_Two) /= 12
     and Imag_Part (Complex_Two) /= -21
        then
           Report.Failed ("Incorrect results from complex operation");
   end if;

   Report.Result;

end Main;
