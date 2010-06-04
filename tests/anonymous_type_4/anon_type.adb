------------------------------------------------------------------------------
--  Test the anonymous type in for statement
--
package body Anon_Type is

   procedure Multiply (X,Y : in Matrix; Z : in out Matrix)
   is
   begin
      -- Z := Matrix'(1 .. 9 => (1 .. 9 =>0));
      for I in 1 .. 9 loop
         for J in 1 .. 9 loop
            for K in 1 .. 9 loop
               Z(I,J) := X(I,K) * Y(K,J);
            end loop;
         end loop;
      end loop;
   end Multiply;

end Anon_Type;
