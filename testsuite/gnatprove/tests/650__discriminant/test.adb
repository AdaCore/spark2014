procedure Test with SPARK_Mode is
   type Small_Nat is new Integer range 0 .. 100;
   subtype Small_Pos is Small_Nat range 1 .. 100;

   type Int_Array is array (Small_Pos range <>) of Integer;

   type R (Length : Small_Nat := 0) is record
      Content : Int_Array (1 .. Length);
   end record;

   procedure P is
      A      : Int_Array (1 .. 100);
      Length : Small_Nat;
      X      : constant R := (Length  => Length,
                              Content => A (1 .. Length));
   begin
      null;
   end P;
begin
   null;
end Test;
