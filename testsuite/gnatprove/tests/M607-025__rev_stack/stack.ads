package Stack is
   type Stack is private;
-- invariants not supported yet
--     with invariant =>
--       Is_Empty (Stack) or else
--       (for all X in integer =>
--        Pop (Push (Stack, X)) = Stack and then Top (Push (Stack, X))  = X);

   function Is_Full(S : Stack) return Boolean;
   function Is_Empty (S : Stack) return Boolean;
   function "=" (S1, S2 : Stack) return Boolean;

   function Top (S : Stack) return Integer with
     Pre => not Is_Empty (S);

   function Pop (S : Stack) return Stack with
     Pre => not Is_Empty (S);

   function Push (S : Stack; X : in Integer) return Stack with
     Pre  => not Is_Full(S),
     Post => Top (Push'Result) = X
       and then Pop (Push'Result) = S;

   procedure Push(S : in out Stack; X : in Integer) with
     Pre  => not Is_Full(S),
     Post => Top (S) = X and Pop (S) = S'Old;

   procedure Pop (S : in out Stack) with
     Pre  => not Is_Empty (S),
     Post => S = Pop (S'old);

private
   type Intarray is array (positive range <>) of integer;
   subtype R1 is integer range 0 .. 10;
   subtype R2 is integer range 1 .. 10;
   type Stack is record
      Top : R1 := 0;
      Content : intarray (R2);
   end record;

   function Is_Full (S : Stack) return Boolean is (S.Top = S.Content'Last);
   function Is_Empty (S : Stack) return Boolean is (S.Top = S.Content'First - 1);
   function Top (S : Stack) return Integer is (S.Content (S.Top));
   function Pop (S : Stack) return Stack is (Stack'(S.Top - 1, S.Content));
   function "=" (S1, S2 : Stack) return Boolean is
     (S1.Top = S2.Top
      and then S1.Content (S1.Content'First .. S1.Top)
                 = S2.Content (S2.Content'First .. S2.Top));

end Stack;
