package Stack is
   Max : constant := 100;
   subtype Index is Integer range 0 .. Max;

--   type Stack (N : Positive)  is private;
   type Stack (N : Index)  is private;

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
--   type Stack (N : Positive) is record
--      Top : Natural  := 0;
--      Content : Intarray (Positive range 1 .. N);
--   end record;
   type Stack (N : Index) is record
      Top : Index;
      Content : Intarray (Index range 1 .. N);
   end record;

   function Top (S : Stack) return Integer is (S.Top);
end Stack;
