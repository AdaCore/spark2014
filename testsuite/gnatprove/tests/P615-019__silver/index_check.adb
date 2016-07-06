procedure Index_Check is

   function Get (S : String; J : Positive) return Character is
   begin
      return S(J);
   end Get;

   procedure Set (S : in out String; J : Positive; C : Character) is
   begin
      S(J) := C;
   end Set;

begin
   null;
end Index_Check;
