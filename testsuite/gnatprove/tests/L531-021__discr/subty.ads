with Basic; use Basic;

package Subty is

   subtype S is R (A);

   procedure P (V : S);
end Subty;
