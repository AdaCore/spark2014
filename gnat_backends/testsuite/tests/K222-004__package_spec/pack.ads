package Pack is
   pragma Annotate (Formal_Proof, On);

   G : access Boolean := new Boolean;

   function F return Boolean
     with Pre => G.all;
   procedure P;
end;
