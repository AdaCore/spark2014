package Pack is
   subtype T is Integer range 1 .. 10;

   procedure Ident (A, B : in out T; C : out T);
end Pack;
