procedure E is
   type R (D : Integer := 1) is null record;

   procedure P (X : out R; Y : out String)
      with Pre => not X'Constrained
   is
      type T is record
         C : Boolean := X'Constrained;
         E : Integer := Y'First;
      end record;
   begin
      X := (D => 1);
      Y := (others => ' ');
   end;
begin
   null;
end;
