package body Q is
   V : Integer := 0;                     --  variable
   C : constant Integer := V;            --  constant with variable input
   function F return Integer is (C);     --  generated Global => (Input => C)
   subtype T is Integer range 1 .. Q.F;  --  this is legal
   --  high bound depends on C, which is known by Entity_Id
end;
