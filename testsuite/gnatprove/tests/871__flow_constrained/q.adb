pragma Initialize_Scalars;

procedure Q is

   type R (D : Integer := 1) is record
      case D is
         when 1 =>
            C : Boolean := True;
         when others =>
            null;
      end case;
   end record;

   type A is array (Positive range 1 .. 3) of R;

   --  References in slice range and array index are evaluated,
   --  but they are fine.

   procedure P_In (X : out A; J,K,L : Positive)
     with Pre => not X (Positive range J .. K) (L)'Constrained
   is
   begin
      X := (others => <>);
   end;

   --  Here evaluation of the same references causes reads of invalid data

   procedure P_Out (X : out A; J,K,L : out Positive)
     with Pre => not X (Positive range J .. K) (L)'Constrained
   is
   begin
      X := (others => <>);
      J := 1;
      K := 2;
      L := 3;
   end;

   X : A;
   J,K,L : Positive;

begin
   P_In  (X, 1, 1, 1);
   P_Out (X, J, K, L);
end;
