procedure Flow
   (Low,  High  : Integer;
    Low1, High1 : Integer;
    L1, L2, L3, H1, H2, H3 : out Integer)
  with Depends =>
        ((L1, H1) => (Low, High),
         (L2, H2) => (Low, High),
         (L3, H3) => (Low1, High1))
is

   procedure Pick (S : out String; L, H : out Integer)
      with Depends => ((S, L, H) => S),
           Post => L = S'First and H = S'Last
   is
   begin
      L := S'First;
      H := S'Last;
      S := (others => ' ');
   end;

   X : String := (Low .. High => 'x');
   subtype Slide is String (Low1 .. High1);

begin
   --  Pass X with its original bounds
   Pick (X,          L1, H1);
   pragma Assert (L1 = Low and H1 = High);

   --  Pass X with a type conversion to an unconstrained type
   Pick (String (X), L2, H2);
   pragma Assert (L2 = Low and H2 = High);

   --  Pass X with a type conversion to a constrained type
   Pick (Slide (X),  L3, H3);
   pragma Assert (L3 = Low1 and H3 = High1);
end;
