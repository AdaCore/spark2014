with Bounded;
with Unbounded;
with Indefinite_Bounded;
with Indefinite_Unbounded;
with Indefinite_Bounded_Tagged;
with Indefinite_Unbounded_Tagged;

procedure Test_Vectors is
begin
   Bounded.Test;
   Unbounded.Test;
   Indefinite_Bounded.Test;
   Indefinite_Unbounded.Test;
   Indefinite_Bounded_Tagged.Test;
   Indefinite_Unbounded_Tagged.Test;
end Test_Vectors;
