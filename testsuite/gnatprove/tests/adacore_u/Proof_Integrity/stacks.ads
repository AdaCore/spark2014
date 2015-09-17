package Stacks with SPARK_Mode is
   type Stack is private;

   Is_Full_E : exception;

   procedure Push (S : in out Stack; E : Natural) with
     Pre  => not Is_Full (S),
     Post => Peek (S) = E;

   function Peek (S : Stack) return Natural;

   function Is_Full (S : Stack) return Boolean;
private

   Max : constant Natural := 100;

   subtype Length_Type is Integer range 0 .. Max;

   type Nat_Array is array (Positive range <>) of Natural;

   type Stack is record
      Top     : Length_Type;
      Content : Nat_Array (1 .. Max);
   end record;

   function Peek (S : Stack) return Natural is
     (if S.Top in S.Content'Range then S.Content (S.Top) else 0);

   function Is_Full (S : Stack) return Boolean is (S.Top >= Max);
end Stacks;
