package Stack is
   pragma Spark_Mode (On);

   Max : constant := 100;

   type Stack  is private;

   package Model is
      type M is array (Positive range <>) of Integer;

      function To (S : Stack) return M with
        Post => To'Result'First = 1 and then To'Result'Last >= 0;
   end Model;

   use Model;

   function Is_Full  (S : Stack) return Boolean is
     (To (S)'Last >= Max);
   function Is_Empty (S : Stack) return Boolean is
     (To (S)'Last < 1);

   function Empty_Stack return Stack with
     Post => Is_Empty (Empty_Stack'Result);

   function Top (S : Stack) return Integer with
     Pre  => not Is_Empty (S),
     Post => Top'Result = To (S) (To (S)'Last);

   procedure Push(S : in out Stack; X : in Integer) with
     Pre  => not Is_Full (S),
     Post => To (S) = To (S)'Old & (1 => X);
--       Post => To (S)'Last = To (S)'Old'Last + 1 and then
--       To (S) (To (S)'Last) = X and then
--       (for all I in To (S)'Old'Range =>
--                    To (S) (I) = To (S)'Old (I));

   procedure Pop (S : in out Stack) with
     Pre  => not Is_Empty (S),
     Post => To (S) = To (S)'Old (1 .. To (S)'Old'Last - 1);
--       Post => To (S)'Last = To (S)'Old'Last - 1 and then
--       (for all I in To (S)'Range =>
--                    To (S) (I) = To (S)'Old (I));

private
   type Intarray is array (positive range <>) of integer;
   subtype R1 is integer range 0 .. Max;
   subtype R2 is integer range R1'First + 1 .. R1'Last;
   type Stack is record
      Top : R1;
      Content : Intarray (R2);
   end record;

   function Top (S : Stack) return Integer is (S.Content (S.Top));
end Stack;
