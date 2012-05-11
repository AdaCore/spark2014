with Gen2;

package body Gen is

   package P2 is new Gen2 (T);

   procedure R (X : T) is
   begin
      pragma Assert (T'Last = X);
      P2.B (X);
   end R;

end Gen;
