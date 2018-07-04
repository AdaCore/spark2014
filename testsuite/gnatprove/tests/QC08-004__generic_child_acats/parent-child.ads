-- Private generic child of Complex_Number.

private

generic

-- No parameter.

package Parent.Child is

   -- ... Other declarations.

   -- Low level operation on complex number.
   function "+" (Left, Right : Complex_Type)
     return Complex_Type;

   function "-" (Right : Complex_Type)
     return Complex_Type;

   -- ... Various other operations in real application.

end Parent.Child;
