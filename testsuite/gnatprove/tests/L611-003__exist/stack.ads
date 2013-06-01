package Stack is

   Max_Size : constant Positive := 100;

   subtype Size_T is Integer range 0 .. Max_Size;

   subtype Element_T is Integer range Natural'First - 1 .. Natural'Last;

   No_Element : constant Element_T := Element_T'First;

   type Stack_T is private;

   function Last_Element (T : Stack_T; S : Size_T) return Element_T;

   function Valid (T : Stack_T; S : Size_T) return Boolean;

   function Size (T : Stack_T) return Size_T
   with Pre => (for Some S in Size_T => Valid (T, S)),
   Post => Valid (T, Size'Result);

   procedure Push (T : in out Stack_T; S : in out Size_T; Value : Natural)
   with Pre => Valid (T, S) and then Size (T) < Max_Size,
   Post => Valid (T, S) and Last_Element (T, S) = Value;

private

   subtype Index_T is Integer range 1 .. Max_Size;

   type Stack_T is array (Index_T) of Element_T;

   function Last_Element (T : Stack_T; S : Size_T) return Element_T is
     (if S > 0 then T (S) else No_Element);

   function Valid (T : Stack_T; S : Size_T) return Boolean is
     ((for all I in Index_T range Index_T'First .. S =>
       T (I) in Natural'Range) and
        (for all I in Index_T range S + 1 .. Index_T'Last =>
         T (I) = No_Element));

end Stack;
