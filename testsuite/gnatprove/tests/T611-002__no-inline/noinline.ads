package Noinline is
   function F return Boolean with No_Inline;

   function G return Boolean;
   pragma No_Inline (G);

   procedure P (X : in out Boolean) with No_Inline;

   procedure Q (X : in out Boolean);
   pragma No_Inline (Q);
end Noinline;
