package P is

   type Nat_Array is array (Positive range <>) of Natural;

   type My_Rec (C : Natural) is record
      Content : Nat_Array (1 .. C);
   end record;

   protected type PP (B : Boolean; C : Natural) is
      function Prot return Boolean;
      procedure P;
   private
      Dummy : Boolean := True;
      R     : My_Rec (C) := (C, Content => (others => 0));
   end;

end;
