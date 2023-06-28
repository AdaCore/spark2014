procedure Global_Havoc (B : Boolean) is
   E : exception;

   type Rec is record
      C : Integer;
   end record;
   --  Type passed neither by-copy nor by-reference

   G : Rec;
   --  This variable is passed as a global to Test, but as a local to Havoc

   procedure Havoc (X : out Rec)
      with Exceptional_Cases => (E => True)
   is
   begin
      if B then  -- dummy condition
         raise E;
      else
         X.C := 123;
      end if;
   end Havoc;

   procedure Test
      with Pre => True,
           Global => (Input => B, Output => G)
   is
   begin
      Havoc (G);  --  G is a global of Test, but is havoced when Havoc raises E
   exception
      when E =>
         pragma Assert (G.C = 123);
   end;
begin
   Test;
end;
