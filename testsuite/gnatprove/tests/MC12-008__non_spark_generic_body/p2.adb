--  Package P2
--
--  As P, but "expands out" the instantiation of the generic G
--  "by hand" into a locally nested package.  Here, setting
--  SPARK_Mode => Off in the body of G works OK, which is
--  inconsistent with the way that the generic version
--  (doesn't) work...
package body P2
  with SPARK_Mode => On
is

   package G
   is
      procedure Op (A : in out T)
        with Pre => A < T'Last;
   end G;

   package body G
     with SPARK_Mode => Off
   is
      procedure Op (A : in out T)
      is
      begin
         A := A + 1;
         
         --  Something not legal SPARK here should be OK,
         --  since this package body is SPARK_Mode => Off
         if A = 1 then
            goto The_End;
         end if;
         
         <<The_End>> null;
      end Op;
   end G;

   --  Call the local package
   procedure Do_It1 (X : in out T)
   is
   begin
      G.Op (X);
   end Do_It1;
   
end P2;
