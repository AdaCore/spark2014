package body Extra with Refined_State => (S => A) is

   A : Integer;

   package N is
      function Foo return Integer;
   private
      B : Integer;  --  we need to warn about this bit of hidden state
   end N;

   package body N is
      function Foo return Integer is (B);
   end N;

end Extra;
