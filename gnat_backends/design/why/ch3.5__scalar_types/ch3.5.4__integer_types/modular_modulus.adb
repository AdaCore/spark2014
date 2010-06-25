with Modular; use Modular;

function Modular_Modulus (A : Integer) return Integer is
   N : Integer := A + Modular.Byte'Modulus;
begin
   return N;
end Modular_Modulus;
