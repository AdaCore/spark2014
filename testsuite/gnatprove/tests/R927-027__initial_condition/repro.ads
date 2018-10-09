package Repro
with
  Abstract_State    => State,
  Initializes       => State,
  Initial_Condition => Invariant
is

   function Invariant return Boolean
   with Ghost;

   procedure Foo
   with
     Pre  => Invariant,
     Post => Invariant;

end Repro;
