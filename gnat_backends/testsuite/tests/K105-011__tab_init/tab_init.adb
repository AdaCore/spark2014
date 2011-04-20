package body Tab_Init is
    Procedure Init (T : out Tab; A : in Integer)
    is
       pragma Annotate (Formal_Proof, On);
    begin
       for I in Tab'First .. Tab'Last loop
          pragma Assert (for all J in Tab'First .. I-1
                           => (T(J) = A*J));
          T(I) := A*I;
          pragma Assert (T(I)=A*I);
       end loop;
    end Init;
end Tab_Init;
