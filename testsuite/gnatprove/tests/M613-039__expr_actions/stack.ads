package Stack is pragma SPARK_Mode (On);
   type Stack  is private;

   package Model is
      type M is array (Positive range <>) of Integer;
      function To (S : Stack) return M;
      function To_But_Top (S : Stack) return M;

      function Is_Full (S : Stack) return Boolean;
      function Is_Empty (S :Stack) return Boolean;
   end Model;
   use Model;

   function Top (S : Stack) return Integer with
     Pre => not Is_Empty (S);

   procedure Push(S : in out Stack; X : in Integer) with
     Pre  => not Is_Full (S),
     Post => Top (S) = X and To_But_Top (S) = To (S'Old);

   procedure Pop (S : in out Stack) with
     Pre  => not Is_Empty (S),
     Post => To_But_Top (S'old) = To (S);

private
   type Intarray is array (positive range <>) of integer;
   subtype R1 is integer range 0 .. 100;
   subtype R2 is integer range R1'First + 1 .. R1'Last;
   type Stack is record
      Top : R1 := 0;
      Content : Intarray (R2);
   end record;

   function Top (S : Stack) return Integer is (S.Top);
end Stack;
