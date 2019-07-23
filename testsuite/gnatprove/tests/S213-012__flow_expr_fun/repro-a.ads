package Repro.A
with
  Abstract_State => State,
  Initializes    => State
is

   type Kind_Type is (Undefined, Defined);
   type Word64 is mod 2 ** 64;

   function Invariant return Boolean
   with
     Ghost,
     Global => (Input => State);

   function Kind (Word : Word64) return Kind_Type
   with
     Global => (Input => State);

   function Is_Undefined (Word : Word64) return Boolean
   with
     Global => (Input => State);

private

   function Is_Undefined (Word : Word64) return Boolean
   is (Kind (Word) = Undefined);

end Repro.A;
