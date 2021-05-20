procedure Expl (B : Boolean)
  with Global => null
is
   X : Integer with Relaxed_Initialization;

   procedure Inner (Y : out Integer) with Pre => True is
   begin
      if B then
         Y := X;
      end if;
      X := 42;
   end Inner;

   type Rec is record
      X : Integer;
   end record;

   procedure Inner2 (Y : out Integer; R : in out Rec) with
     Pre => True, Relaxed_Initialization => R
   is
   begin
      if B then
         Y := R.X;
      end if;
      R.X := 42;
   end Inner2;

   Z : Integer;
   S : Rec with Relaxed_Initialization;
begin
   Inner (Z);
   Z := X;

   Inner2 (Z, S);
   Z := S.X;
end Expl;
