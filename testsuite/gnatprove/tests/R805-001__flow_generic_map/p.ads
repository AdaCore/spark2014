package P is
   V : Integer := 0;
   C : constant Integer := V;

   generic
      A : Integer;
   package Gen is
      function F return Integer is (A) with Global => A;
      --  Inside the instance A will become a constant; fine.
   end;

   package Inst is new Gen (A => C);

   function G return Integer is (Inst.F) with Global => C;
   --  Outside the instance that constant must be "substituted" with objects
   --  used to initialize it, i.e. A should be substituted with C.
end;
