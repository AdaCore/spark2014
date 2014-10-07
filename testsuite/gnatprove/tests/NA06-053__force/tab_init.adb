package body Tab_Init is
   procedure Init (T : out Tab; A : in Integer) is
   begin
      for I in Tab'First .. Tab'Last loop
         T(I) := A*I;
         pragma Loop_Invariant (for all J in Tab'First .. I
                                  => (T(J) = A*J));
         pragma Assert (T(I)=A*I);
      end loop;
   end Init;
end Tab_Init;
