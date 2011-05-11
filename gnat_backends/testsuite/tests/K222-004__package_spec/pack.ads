package Pack is
   pragma Annotate (gnatprove, Force);

   G : access Boolean := new Boolean;

   function F return Boolean
     with Pre => G.all;
   procedure P;
end;
