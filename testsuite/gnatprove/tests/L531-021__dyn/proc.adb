procedure Proc is
   type T is range 1 .. 10;

   type A is array (T range <>) of Integer;

   type R (Length : T) is record
      Contents : A (1 .. Length);
   end record;

   function F (X : Integer) return A is
   begin
      if X = 1 then
         return (1 .. 2 => 3);
      else
         return (1 .. 3 => 4);
      end if;
   end F;

   procedure P is
      Item : A := F (3);
      Dr   : R := (Item'Length, Item);
   begin
      null;
   end P;

begin
   null;
end;
