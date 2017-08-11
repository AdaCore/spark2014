package Pkg is

   package Nested with Abstract_State => State is
      function Get return Boolean with Post => Get'Result;
   private
      X : Boolean := True with Part_Of => State;
   end;

end;
