with Superstrings;

package Strbound is

   generic
      Max : Positive;
      --  Maximum length of a Bounded_String

   package Generic_Bounded_Length is

      Max_Length : constant Positive := Max;

      type Bounded_String is private;


      function "="
        (Left  : Bounded_String;
         Right : Bounded_String) return Boolean;

      procedure P;


   private

      type Bounded_String is new Superstrings.Super_String (Max_Length);

      overriding function "="
        (Left  : Bounded_String;
         Right : Bounded_String) return Boolean
         renames Equal;

   end Generic_Bounded_Length;

end Strbound;
