package body P is

   procedure Init (X : out A) is
   begin
      X := (others => 0);
      X (1) := X'Last;
      X (20) := -1;
  end Init;

end P;
